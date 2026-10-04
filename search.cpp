/*****************************************************************************
!!  SAT01 solver: the search                                                !!
!!  Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

#include <limits.h>
#include <string>
#include <utility>
#include <vector>

#include "sat01.h"

using namespace std;

// guess_weight() ranks the variables in equally many equations: the fewer
// equations the foes of a variable are in, the better
static int guess_weight(const Sat01& sat01, int v) {
  int weight = 0;
  for(int k : sat01.vars[v].foes.ones()) weight -= (int)sat01.vars[k].equations.size();
  return weight;
}

// choose_guess() picks the variable in the most equations, of those the one
// of the greatest guess_weight(), and of those the first
static int choose_guess(const Sat01& sat01) {
  int best = 0;
  int best_weight = INT_MIN;  // not computed yet
  for(int v=1;v<(int)sat01.vars.size();++v) {
    size_t size = sat01.vars[v].equations.size();
    size_t best_size = sat01.vars[best].equations.size();
    if(size>best_size) {
      best = v;
      best_weight = INT_MIN;
    } else if(size==best_size) {
      if(best_weight==INT_MIN) best_weight = guess_weight(sat01,best);
      int weight = guess_weight(sat01,v);
      if(weight>best_weight) {
        best = v;
        best_weight = weight;
      }
    }
  }
  return best;
}

// Each guess makes the chosen variable true; a contradiction backtracks to
// the last guess still open and makes its variable false instead.  The state
// to backtrack to is kept in memory, as a copy of the instance at the guess.
bool solve(Sat01& sat01, int& depth, int& max_depth, int& n_guess,
           const char* dump_dir) {
  depth = max_depth = n_guess = 0;
  vector<pair<Sat01,int>> open;  // the instance at each open guess, and its variable
  for(;;) {
    int guess = choose_guess(sat01);
    printf("Guess:\n%s\n",sat01.vars[guess].name.c_str());
    ++n_guess;
    if(dump_dir) {
      string name = string(dump_dir)+"/guess"+to_string(n_guess)+"_depth"+
        to_string(depth)+".sat01";
      sat01.save_bin(name.c_str());
    }
    open.emplace_back(sat01,guess);
    if(++depth>max_depth) max_depth = depth;
    printf("Depth=%d\n",depth);
    Status status = sat01.assign(guess,Value::True);
    if(status==Status::contradiction) puts("Backtracking ...");
    while(status==Status::contradiction && depth) {
      sat01 = std::move(open.back().first);
      int v = open.back().second;
      open.pop_back();
      --depth;
      printf("%d variables, %d equations\n",(int)sat01.vars.size(),(int)sat01.equs.size());
      printf("Depth=%d\n",depth);
      status = sat01.assign(v,Value::False);
    }
    if(status!=Status::open) return status==Status::solved;
  }
}
