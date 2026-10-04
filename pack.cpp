/*****************************************************************************
!!  SAT01 solver: packing of the instance                                   !!
!!  Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

#include <bit>

#include "sat01.h"

using namespace std;

// remove_variable() takes an assigned variable v out of the foes of the free
// variables, shifting the entries above v down, and out of its equations
void Sat01::remove_variable(int v) {
  for(Variable& other : vars)
    if(other.value==Value::Free) other.foes.erase(v);
  for(int e : vars[v].equations) erase_sorted(equs[e].vars,v);
}

// twins() tells whether u < v are twins: free variables that do not
// contradict each other and have the same foes among the variables that stay,
// i.e. those above v, which are free by now, and the free ones below it.  The
// variables above v that are gone have already been removed from the foes.
// Twins take the same value in every solution: all the other variables of
// the equations of either are foes of both.
bool Sat01::twins(int v, int u) const {
  const bool_vector& a = vars[v].foes;
  const bool_vector& b = vars[u].foes;
  for(int w=0;w<a.n_words();++w)
    for(bool_vector::word d=a.words()[w]^b.words()[w];d;d&=d-1) {
      int p = w*bool_vector::word_bits+countr_zero(d);
      if(p>=v || vars[p].value==Value::Free) return false;
    }
  return true;
}

// merge_twin() merges the twin u into v: v takes the place of u in its
// equations and adds its name, and u, now false, goes when pack() reaches it
void Sat01::merge_twin(int v, int u) {
  Variable& var = vars[v];
  Variable& twin = vars[u];
  var.name += '\n';
  var.name += twin.name;
  twin.value = Value::False;
  for(int t=(int)twin.equations.size()-1;t>=0;--t) {
    int e = twin.equations[t];
    erase_sorted(equs[e].vars,u);
    insert_sorted(equs[e].vars,v);
    insert_sorted(var.equations,e);
  }
  twin.equations.clear();
}

void Sat01::pack() {
  // the variables from the last to the first: an assigned one is removed (a
  // true one leaving its name to ones), a free one merges its twins below it
  vector<int> kept;  // the free variables, descending
  kept.reserve(n_unassigned);
  for(int v=(int)vars.size()-1;v>=0;--v) {
    switch(vars[v].value) {
      case Value::True:
        ones.push_back(vars[v].name);
        remove_variable(v);
        break;
      case Value::Free:
        for(int u=0;u<v;++u)
          if(vars[u].value==Value::Free && twins(v,u)) merge_twin(v,u);
        kept.push_back(v);
        break;
      default:
        remove_variable(v);
    }
  }
  n_unassigned = (int)kept.size();

  // an equation equal to a later one goes
  for(int e1=1;e1<(int)equs.size();++e1) {
    if(!equs[e1].unassigned) continue;
    for(int e2=0;e2<e1;++e2)
      if(equs[e2].unassigned && equs[e1].vars==equs[e2].vars) {
        for(int v : equs[e1].vars) erase_sorted(vars[v].equations,e2);
        equs[e2].unassigned = 0;
      }
  }

  // the variables kept move down to 0, 1, ..., in their order
  reverse(kept.begin(),kept.end());
  vector<int> new_var(vars.size(),-1);
  for(int t=0;t<(int)kept.size();++t) {
    new_var[kept[t]] = t;
    if(kept[t]!=t) vars[t] = std::move(vars[kept[t]]);
  }
  vars.resize(kept.size());

  // so do the equations left, which are those with variables unassigned
  vector<int> new_equ(equs.size(),-1);
  int m = 0;
  for(int e=0;e<(int)equs.size();++e) {
    if(!equs[e].unassigned) continue;
    if(m<e) equs[m] = std::move(equs[e]);
    for(int& v : equs[m].vars) v = new_var[v];
    new_equ[e] = m;
    ++m;
  }
  equs.resize(m);
  for(Variable& var : vars)
    for(int& e : var.equations) e = new_equ[e];

  printf("%d variables, %d equations remain\n",n_unassigned,m);
}
