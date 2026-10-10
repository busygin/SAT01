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
// non-edges, which are 0 in the standard wrapper and z_i z_j - m M_ij/(z_i z_j)
// in H_A, M_ij the number of equations i and j share: H_A ignores the
// contradictions between variables of no common equation (2-clauses), those
// of the instance and those propagation derives.
//
// The top eigenspace of H_A is degenerate and holds every solution, so the
// Douglas-Rachford stage of qualex_ms() (QMS_DR) iterates on the sphere of
// stationary points that holds them.  Its projection onto the nonnegative
// orthant cannot single them out, since a nonnegative point there need not
// respect the 2-clauses; -D replaces it by the greedy 2-clause projection
// (see two_clause_projection()) and asks for 300 iterations unless QMS_DR
// says otherwise.  -W drives the points onto the surface of the standard
// clique wrapper H_0 as well, {x^T H_0 x = 1, z^T x = 1}, on which every
// solution lies too (Douglas-Rachford then runs between the product of the
// sphere and that surface and the diagonal of the orthant or of the 2-clause
// set, or with QMS_DR_CONCUR in the product space of the three sets, see
// try_dr_points()).  H_0 is proper, so the sphere, the orthant and its surface
// meet exactly in the solutions.  The other QMS_* switches of
// qualex-ms apply too, QMS_META_N among them, which with -m adds the Meta-NBIW
// stage on that many of the best multipliers at the radius of m.
//
// A clique of weight m is checked against the original instance and written
// to <base>.qms.out in the format of the solver's .out files.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <algorithm>
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

// share_equation() tells whether two variables are in a common equation
static bool share_equation(const Variable& a, const Variable& b) {
  vector<int>::const_iterator i = a.equations.begin(), j = b.equations.begin();
  while(i!=a.equations.end() && j!=b.equations.end()) {
    if(*i==*j) return true;
    if(*i<*j) ++i;
    else ++j;
  }
  return false;
}

// two_clause_projection() is the projection, for the variables left (vertex t
// being variable residual[t]), onto the nonnegative points whose support has no
// 2-clause, i.e. no two contradicting variables of no common equation, done
// greedily as jam.py's clause_projector(): the entries not positive go, and the
// others are kept from the largest down unless they 2-clash with one kept
// before.  Within an equation the sphere of H_A already holds the equation
// sums equal, so only the 2-clauses are left to the projection.
static Projection two_clause_projection(const Sat01& sat01, const vector<int>& residual) {
  int n = (int)residual.size();
  vector<int> vertex(sat01.vars.size(),-1);
  for(int t=0;t<n;++t) vertex[residual[t]] = t;
  vector<vector<int>> clashes(n);  // the 2-clause partners of each vertex
  for(int t=0;t<n;++t) {
    const Variable& var = sat01.vars[residual[t]];
    for(int v : var.foes.ones())
      if(vertex[v]>=0 && !share_equation(var,sat01.vars[v])) clashes[t].push_back(vertex[v]);
  }
  vector<int> order(n);
  vector<char> blocked(n);
  return [clashes,order,blocked](double* y, int n) mutable {
    int k = 0;
    for(int i=0;i<n;++i) {
      if(y[i]>0.0) order[k++] = i;
      else y[i] = 0.0;
    }
    sort(order.begin(),order.begin()+k,[y](int i, int j) { return y[i]>y[j]; });
    fill(blocked.begin(),blocked.end(),0);
    for(int t=0;t<k;++t) {
      int i = order[t];
      if(blocked[i]) {
        y[i] = 0.0;
        continue;
      }
      for(int j : clashes[i]) blocked[j] = 1;
    }
  };
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
  bool standard = false, at_m = false, clause_dr = false, standard_surface = false;
  const char* name = nullptr;
  for(int a=1;a<argc;++a) {
    if(!strcmp(argv[a],"-s")) standard = true;
    else if(!strcmp(argv[a],"-m")) at_m = true;
    else if(!strcmp(argv[a],"-D")) clause_dr = true;
    else if(!strcmp(argv[a],"-W")) standard_surface = true;
    else name = argv[a];
  }
  if(!name) {
    puts("Syntax: sat01qms [-s] [-m] [-D] [-W] <sat01_file>\n"
         "Runs the full propagation of the SAT01 solver and then QUALEX-MS, without\n"
         "search, on the clique problem left: the free variables weighted by their\n"
         "numbers of equations, adjacent iff they do not contradict.  QUALEX-MS works\n"
         "with the equation wrapper, or with -s with the standard clique wrapper, and\n"
         "with -m takes its stationary points at the radius of a clique of weight m\n"
         "(the number of equations), the weight of a solution, with the method of\n"
         "QUALEX-MS 1.2.  -D runs its Douglas-Rachford stage (QMS_DR, 300 iterations\n"
         "unless set) with the 2-clause projection instead of the orthant, and -W\n"
         "(the same iterations) drives its points onto the surface of the standard\n"
         "clique wrapper as well.  A clique of weight m is a solution, which is\n"
         "checked against the instance and written to <base>.qms.out.");
    return 1;
  }
  const char* wrapper = standard ? "standard" : "equation";
  const char* radius = at_m ? "m" : "anchor";
  if(clause_dr || standard_surface) setenv("QMS_DR","300",0);
  string dr_sets = getenv("QMS_DR")==nullptr || atoi(getenv("QMS_DR"))<=0 ? "off" :
                   clause_dr ? "clause" : "orthant";
  if(standard_surface && dr_sets!="off") dr_sets += "+standard";
  const char* dr = dr_sets.c_str();

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
    printf("RESULT %s wrapper=%s radius=%s dr=%s decided=%s propagation=%.2fs\n",name,
           wrapper,radius,dr,status==Status::solved ? "sat" : "unsat",propagation_seconds);
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
    DRTargets targets;
    Projection clause;
    if(clause_dr) {
      clause = two_clause_projection(sat01,residual);
      targets.projection = &clause;
    }
    if(standard_surface) {  // made before qualex_ms() decomposes a (see wrapper_surface())
      vector<double> a0((size_t)g.n*g.n);
      build_wrapper(g,info,a0.data());
      targets.surfaces.push_back(wrapper_surface(info,a0.data()));
    }
    // with -m, the clique sought on the vertices left weighs m less what
    // preprocessing preselected
    qualex_ms(info,a.data(),at_m ? m-preselected_weight : 0.0,&targets);
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
  printf("RESULT %s wrapper=%s radius=%s dr=%s n=%d m=%d preselected=%d left=%d "
         "greedy=%g weight=%g solution=%d verified=%s propagation=%.2fs qms=%.2fs\n",
         name,wrapper,radius,dr,n,m,n_preselected,n_left,greedy_weight,clique_weight,
         (int)solution,verified,propagation_seconds,qms_seconds);
  return 0;
}
