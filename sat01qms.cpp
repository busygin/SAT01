/*****************************************************************************
!!  sat01qms: QUALEX-MS on a propagated SAT01 instance                       !!
!!  Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

// sat01qms runs the full propagation of the solver on an instance and then,
// without any search, QUALEX-MS on what is left.  The vertices are the free
// variables, each weighted by the number of its equations, and two of them
// are adjacent iff they do not contradict, so that a clique of weight m, the
// number of equations, is a solution.  The pipeline is that of the qualex-ms
// program: preproc_clique(), Meta-NBIW, and the trust region stage
// qualex_ms(), on the equation wrapper (by default)
//   H_A = z z^T + m (I - D^{-1/2} A^T A D^{-1/2}),  D = diag(w), z = sqrt(w),
// in which every solution is anchored at level m, or with -s on the standard
// clique wrapper.  QUALEX-MS takes its stationary points around the radius of
// a clique one w_min heavier than its incumbent; with -m it takes them at the
// radius of a clique of weight m, which is what a solution weighs, with the
// method of QUALEX-MS 1.2 (see qualex_ms()).  The wrappers differ only on the
// non-edges, which are 0 in the
// standard wrapper and z_i z_j - m M_ij/(z_i z_j) in H_A, M_ij the number of
// equations i and j share: H_A ignores the contradictions between variables
// of no common equation, those of the instance and those propagation derives.
// The QMS_* switches of qualex-ms apply: QMS_DR among them, off unless set, and
// QMS_META_N, which with -m adds the Meta-NBIW stage on that many of the best
// multipliers at the radius of m.
//
// A clique of weight m is checked against the original instance and written
// to <base>.qms.out in the format of the solver's .out files.

#include <stdio.h>
#include <string.h>
#include <chrono>
#include <exception>
#include <list>
#include <string>
#include <unordered_map>
#include <vector>

#include "graph.h"
#include "greedy_clique.h"
#include "preproc_clique.h"
#include "qualex.h"
#include "wrapper.h"

#include "sat01.h"

using namespace std;

// build_equation_wrapper() fills a with H_A - w_min I (the form qualex_ms()
// takes) for the variables preproc_clique() has left, vertex t being variable
// residual[t].  A is restricted to them: the variables it preselected are
// compatible with every one left, so the equations of those left are exactly
// the ones not covered yet, m counts them, and each variable left keeps its
// weight.
static void build_equation_wrapper(const Sat01& sat01, const vector<int>& residual,
                                   MaxCliqueInfo& info, double* a) {
  int n = info.g.n;
  vector<int> vertex(sat01.vars.size(),-1);
  for(int t=0;t<n;++t) vertex[residual[t]] = t;
  vector<vector<int>> rows;  // the equations with a variable left, as vertices
  for(const Equation& equ : sat01.equs) {
    vector<int> row;
    for(int v : equ.vars)
      if(vertex[v]>=0) row.push_back(vertex[v]);
    if(!row.empty()) rows.push_back(row);
  }
  double m = (double)rows.size();
  const double* z = info.sqrtw;
  for(int t=0;t<n;++t) {
    for(int u=0;u<n;++u) a[(size_t)t*n+u] = z[t]*z[u];
    a[(size_t)t*n+t] = info.g.weights[t]-info.w_min;
  }
  // each equation shared takes m/(z_t z_u) off entry (t,u)
  for(const vector<int>& row : rows)
    for(int t : row)
      for(int u : row)
        if(t!=u) a[(size_t)t*n+u] -= m/(z[t]*z[u]);
}

// split_names() adds the names of a variable, those of merged twins being
// joined by '\n', to names
static void split_names(const string& name, vector<string>& names) {
  size_t first = 0, end;
  while((end = name.find('\n',first))!=string::npos) {
    names.push_back(name.substr(first,end-first));
    first = end+1;
  }
  names.push_back(name.substr(first));
}

// verify() checks a solution, given by the names of its true variables,
// against the instance in file_name: every equation has exactly one of them,
// and no two of them contradict
static bool verify(const char* file_name, const vector<string>& true_names) {
  Sat01 original;
  original.load_bin(file_name);
  unordered_map<string,int> index;
  for(int v=0;v<(int)original.vars.size();++v) index[original.vars[v].name] = v;
  vector<char> value(original.vars.size(),0);
  for(const string& name : true_names) {
    unordered_map<string,int>::iterator p = index.find(name);
    if(p==index.end()) {
      printf("verify: no variable %s\n",name.c_str());
      return false;
    }
    value[p->second] = 1;
  }
  for(int e=0;e<(int)original.equs.size();++e) {
    int hits = 0;
    for(int v : original.equs[e].vars) hits += value[v];
    if(hits!=1) {
      printf("verify: equation %d has %d true variables\n",e+1,hits);
      return false;
    }
  }
  for(int v=0;v<(int)original.vars.size();++v) {
    if(!value[v]) continue;
    for(int u : original.vars[v].foes.ones())
      if(value[u]) {
        printf("verify: %s and %s contradict\n",original.vars[v].name.c_str(),
               original.vars[u].name.c_str());
        return false;
      }
  }
  return true;
}

static double seconds_since(chrono::steady_clock::time_point t) {
  return chrono::duration<double>(chrono::steady_clock::now()-t).count();
}

int main(int argc, char** argv) {
  bool standard = false, at_m = false;
  const char* name = nullptr;
  for(int a=1;a<argc;++a) {
    if(!strcmp(argv[a],"-s")) standard = true;
    else if(!strcmp(argv[a],"-m")) at_m = true;
    else name = argv[a];
  }
  if(!name) {
    puts("Syntax: sat01qms [-s] [-m] <sat01_file>\n"
         "Runs the full propagation of the SAT01 solver and then QUALEX-MS, without\n"
         "search, on the clique problem left: the free variables weighted by their\n"
         "numbers of equations, adjacent iff they do not contradict.  QUALEX-MS works\n"
         "with the equation wrapper, or with -s with the standard clique wrapper, and\n"
         "with -m takes its stationary points at the radius of a clique of weight m\n"
         "(the number of equations), the weight of a solution, with the method of\n"
         "QUALEX-MS 1.2.  A clique of weight m is a solution, which is checked\n"
         "against the instance and written to <base>.qms.out.");
    return 1;
  }
  const char* wrapper = standard ? "standard" : "equation";
  const char* radius = at_m ? "m" : "anchor";

  Sat01 sat01;
  try {
    sat01.load_bin(name);
  }
  catch(const exception& error) {
    printf("ERROR: %s\n",error.what());
    return 1;
  }

  chrono::steady_clock::time_point start = chrono::steady_clock::now();
  Status status = sat01.preprocess();
  double propagation_seconds = seconds_since(start);
  if(status!=Status::open) {
    puts(status==Status::solved ? "A solution has been found by the propagation."
                                : "The propagation has revealed that no solution exists.");
    printf("RESULT %s wrapper=%s radius=%s decided=%s propagation=%.2fs\n",name,wrapper,
           radius,status==Status::solved ? "sat" : "unsat",propagation_seconds);
    return 0;
  }

  // the clique problem of the variables left
  int n = (int)sat01.vars.size(), m = (int)sat01.equs.size();
  Graph g(n);
  for(int v=0;v<n;++v) g.weights[v] = (double)sat01.vars[v].equations.size();
  for(int v=0;v<n;++v)
    for(int u=v+1;u<n;++u)
      if(!sat01.vars[v].foes.at(u)) g.add_edge(v,u);

  // the pipeline of qualex-ms (see its main())
  start = chrono::steady_clock::now();
  vector<int> residual;
  list<int> preselected, clique;
  double clique_weight;
  double preselected_weight = preproc_clique(g,residual,preselected,clique_weight,clique);
  int n_preselected = (int)preselected.size(), n_left = (int)residual.size();
  double greedy_weight = clique_weight;
  if(!residual.empty()) {
    MaxCliqueInfo info(g,true);
    info.verbose = false;
    meta_greedy_clique(info);
    if(info.lower_clique_bound>greedy_weight) greedy_weight = info.lower_clique_bound;
    vector<double> a((size_t)g.n*g.n);
    if(standard) build_wrapper(g,info,a.data());
    else build_equation_wrapper(sat01,residual,info,a.data());
    // with -m, the clique sought on the vertices left weighs m less what
    // preprocessing preselected
    qualex_ms(info,a.data(),at_m ? m-preselected_weight : 0.0);
    if(info.lower_clique_bound>clique_weight) {
      clique_weight = info.lower_clique_bound;
      clique.clear();
      for(int t : info.clique) clique.push_back(residual[t]);
    }
  }
  clique.splice(clique.begin(),preselected);
  clique_weight += preselected_weight;
  greedy_weight += preselected_weight;
  double qms_seconds = seconds_since(start);

  bool solution = clique_weight>=m;
  const char* verified = "-";
  if(solution) {
    for(Variable& var : sat01.vars) var.value = Value::False;
    for(int v : clique) sat01.vars[v].value = Value::True;
    vector<string> true_names;
    for(const string& one : sat01.ones) split_names(one,true_names);
    for(int v : clique) split_names(sat01.vars[v].name,true_names);
    verified = verify(name,true_names) ? "yes" : "NO";
    string out(name);
    size_t ext = out.rfind(".sat01");
    if(ext!=string::npos) out.erase(ext);
    out += ".qms.out";
    FILE* file = fopen(out.c_str(),"w");
    if(file) {
      sat01.print_solution(file);
      fclose(file);
    }
  }
  printf("QUALEX-MS on the %s wrapper, radius %s: weight %g of m = %d (%s), Meta-NBIW %g\n",
         wrapper,at_m ? "of m" : "around the incumbent's",clique_weight,m,
         solution ? "a solution" : "no solution",greedy_weight);
  printf("RESULT %s wrapper=%s radius=%s n=%d m=%d preselected=%d left=%d greedy=%g "
         "weight=%g solution=%d verified=%s propagation=%.2fs qms=%.2fs\n",
         name,wrapper,radius,n,m,n_preselected,n_left,greedy_weight,clique_weight,
         (int)solution,verified,propagation_seconds,qms_seconds);
  return 0;
}
