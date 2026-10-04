/*****************************************************************************
!!  SAT01 solver: propagation                                               !!
!!  Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

// Propagation draws three kinds of conclusions:
//   unit propagation: the foes of a true variable are false, and the last
//     candidate of an equation is true;
//   covering (clique) analysis: a variable contradicting every free variable
//     of an equation is false;
//   contradiction analysis: assuming a variable v true makes its foes false
//     (Excluded); if an equation is then left with a single free variable u,
//     the foes of u contradict v, if it is left with none, v is false, and a
//     variable covering what it is left with contradicts v.

#include <bit>

#include "sat01.h"

using namespace std;

// eliminate_one() eliminates the assigned variable v.  A true v makes its free
// foes false and satisfies its equations.  A false v leaves each of its
// equations with one candidate fewer: an unsatisfied equation left with none
// is a contradiction, one left with a single candidate makes it true, and one
// left with more goes to modified for the covering analysis.  Every variable
// this assigns goes to queue.
Status Sat01::eliminate_one(int v, deque<int>& queue, deque<int>& modified) {
  Variable& var = vars[v];
  if(var.value==Value::True) {
    for(int k : var.foes.ones()) {
      Variable& foe = vars[k];
      if(foe.value==Value::True) return Status::contradiction;
      if(foe.value==Value::Free) {
        if(trace) fprintf(trace,"%s is false by unit propagation\n",foe.name.c_str());
        foe.value = Value::False;
        queue.push_back(k);
      }
    }
    for(int e : var.equations) {
      --equs[e].unassigned;
      equs[e].satisfied = true;
    }
    return Status::open;
  }
  for(int e : var.equations) {
    Equation& equ = equs[e];
    --equ.unassigned;
    if(equ.satisfied) continue;
    if(equ.unassigned==0) return Status::contradiction;
    if(equ.unassigned==1) {
      // the first variable not false is the last candidate, which must be true
      // (it may be true already, waiting in the queue)
      int last = -1;
      for(int u : equ.vars)
        if(vars[u].value!=Value::False) { last = u; break; }
      if(last>=0) {
        if(vars[last].value==Value::Free) {
          if(trace) fprintf(trace,"%s is true by unit propagation\n",vars[last].name.c_str());
          vars[last].value = Value::True;
          queue.push_back(last);
        }
        continue;
      }
    }
    if(!equ.modified) {
      equ.modified = true;
      modified.push_back(e);
    }
  }
  return Status::open;
}

// eliminate() eliminates the variables of queue in turn, and what that
// assigns in its turn
Status Sat01::eliminate(deque<int>& queue, deque<int>& modified) {
  while(!queue.empty()) {
    Status status = eliminate_one(queue.front(),queue,modified);
    if(status!=Status::open) return status;
    --n_unassigned;
    queue.pop_front();
  }
  return n_unassigned==0 ? Status::solved : Status::open;
}

// find_covering_vars() looks at the free variables of equation e.  With none
// or one (single) it says so; otherwise it appends to coverings, ascending, the
// free variables contradicting all of them.
Cover Sat01::find_covering_vars(int e, int& single, deque<int>& coverings) {
  vector<const bool_vector*> free_foes;  // the foes of each free variable of e
  for(int v : equs[e].vars)
    if(vars[v].value==Value::Free) {
      single = v;
      free_foes.push_back(&vars[v].foes);
    }
  if(free_foes.empty()) return Cover::no_free;
  if(free_foes.size()==1) return Cover::one_free;
  int n_words = free_foes[0]->n_words();
  for(int k=0;k<n_words;++k) {
    bool_vector::word common = free_foes[0]->words()[k];
    for(size_t t=1;common && t<free_foes.size();++t) common &= free_foes[t]->words()[k];
    for(;common;common&=common-1) {
      int v = k*bool_vector::word_bits+countr_zero(common);
      if(vars[v].value==Value::Free) coverings.push_back(v);
    }
  }
  return Cover::covered;
}

// cover() runs the covering analysis of equation e: the free variables
// covering it are false, and are eliminated along with what follows, which
// may modify further equations
Status Sat01::cover(int e, deque<int>& queue, deque<int>& modified) {
  int single;
  switch(find_covering_vars(e,single,queue)) {
    // eliminate() leaves every equation either satisfied or with two free
    // variables or more, so the first two cases do not arise here
    case Cover::no_free:
      return Status::contradiction;
    case Cover::one_free:
      vars[single].value = Value::True;
      queue.push_back(single);
      break;
    case Cover::covered:
      for(int v : queue) {
        if(trace) fprintf(trace,"%s is false by covering equation %d\n",vars[v].name.c_str(),e+1);
        vars[v].value = Value::False;
      }
  }
  return eliminate(queue,modified);
}

// cover_modified() runs the covering analysis on the equations of modified,
// in turn, until none is left
Status Sat01::cover_modified(deque<int>& queue, deque<int>& modified) {
  while(!modified.empty()) {
    int e = modified.front();
    modified.pop_front();
    equs[e].modified = false;
    if(!equs[e].unassigned) continue;
    Status status = cover(e,queue,modified);
    if(status!=Status::open) return status;
  }
  return Status::open;
}

// eliminate_assigned() starts preprocessing: an equation with no variable is a
// contradiction and one with a single variable makes it true, the assigned
// variables are eliminated, and every equation goes through the covering
// analysis, in order and then as long as eliminations modify any
Status Sat01::eliminate_assigned() {
  deque<int> queue, modified;
  for(Equation& equ : equs) {
    switch(equ.unassigned) {
      case 0:
        return Status::contradiction;
      case 1: {
        Variable& var = vars[equ.vars[0]];
        if(var.value==Value::False) return Status::contradiction;
        var.value = Value::True;
        break;
      }
      default:
        equ.modified = true;  // keeps eliminate() from queueing it twice
    }
  }
  for(int v=0;v<(int)vars.size();++v)
    if(vars[v].value!=Value::Free) queue.push_back(v);
  Status status = eliminate(queue,modified);
  if(status!=Status::open) return status;
  for(int e=0;e<(int)equs.size();++e) {
    equs[e].modified = false;
    if(!equs[e].unassigned) continue;
    status = cover(e,queue,modified);
    if(status!=Status::open) return status;
  }
  return cover_modified(queue,modified);
}

// initial_tests() gives every free variable the equations of its free foes
// for its contradiction analysis, leaving out its own
Tests Sat01::initial_tests() {
  Tests tests;
  vector<char> seen(equs.size(),0);
  for(int v=0;v<(int)vars.size();++v) {
    Variable& var = vars[v];
    if(var.value!=Value::Free) continue;
    vector<int>& to_test = tests.emplace_hint(tests.end(),v,vector<int>())->second;
    for(int e : var.equations) seen[e] = 1;
    for(int k : var.foes.ones()) {
      if(vars[k].value!=Value::Free) continue;
      for(int e : vars[k].equations)
        if(!seen[e]) {
          insert_sorted(to_test,e);
          seen[e] = 1;
        }
    }
    for(int e : var.equations) seen[e] = 0;
    for(int e : to_test) seen[e] = 0;
  }
  return tests;
}

// import_modified() passes the equations eliminations have modified on to
// the contradiction analysis: an equation goes to the tests of every variable
// outside it that contradicts at least half of its free variables
void Sat01::import_modified(deque<int>& modified, Tests& tests) {
  while(!modified.empty()) {
    int e = modified.front();
    modified.pop_front();
    Equation& equ = equs[e];
    equ.modified = false;
    if(!equ.unassigned) continue;
    vector<const bool_vector*> free_foes;
    for(int v : equ.vars)
      if(vars[v].value==Value::Free) {
        free_foes.push_back(&vars[v].foes);
        vars[v].flag = true;  // in the equation
      }
    int n_words = vars[equ.vars[0]].foes.n_words();
    for(int k=0;k<n_words;++k) {
      // how many free variables of e each variable of word k contradicts
      int count[bool_vector::word_bits] = {0};
      for(const bool_vector* foes : free_foes)
        for(bool_vector::word w=foes->words()[k];w;w&=w-1) ++count[countr_zero(w)];
      for(int b=0;b<bool_vector::word_bits;++b) {
        if(2*count[b]<equ.unassigned) continue;
        Variable& var = vars[k*bool_vector::word_bits+b];
        // the variables of e contradict all the others, so this meets each
        // of them, which clears its flag
        if(!var.flag) insert_unique(tests[k*bool_vector::word_bits+b],e);
        else var.flag = false;
      }
    }
  }
}

// add_tests() adds equations to the tests of variable v
static void add_tests(Tests& tests, int v, const vector<int>& equations) {
  Tests::iterator p = tests.lower_bound(v);
  if(p==tests.end() || p->first!=v) tests.insert(p,Tests::value_type(v,equations));
  else for(int e : equations) insert_unique(p->second,e);
}

// propagate() runs the contradiction analysis of each variable with tests to
// make, in increasing order, until none is left.  Assuming a free variable v
// true excludes its free foes; then, for each equation to test, taken from the
// last,
//   a single free variable u left means that v true makes u true, so the
//     foes of u that are free contradict v (and their equations are tested);
//   no free variable left means v is false, which is eliminated;
//   two or more mean that the variables covering them contradict v.
// A new contradiction gives the other variable the equations of v to test.
Status Sat01::propagate(Tests& tests) {
  deque<int> queue, modified;
  while(!tests.empty()) {
    Tests::iterator p = tests.begin();
    int v = p->first;
    Variable& var = vars[v];
    if(var.value==Value::Free) {
      for(int k : var.foes.ones())
        if(vars[k].value==Value::Free) vars[k].value = Value::Excluded;
      vector<int>& to_test = p->second;
      bool eliminated = false;
      while(!to_test.empty() && !eliminated) {
        int e = to_test.back();
        to_test.pop_back();
        if(!equs[e].unassigned) continue;
        int single;
        switch(find_covering_vars(e,single,queue)) {
          case Cover::one_free: {
            const bool_vector& single_foes = vars[single].foes;
            for(int w=0;w<var.foes.n_words();++w) {
              // the foes of single that are new to v
              bool_vector::word fresh = single_foes.words()[w] & ~var.foes.words()[w];
              for(;fresh;fresh&=fresh-1) {
                int k = w*bool_vector::word_bits+countr_zero(fresh);
                Variable& foe = vars[k];
                if(foe.value!=Value::Free) continue;
                if(trace) fprintf(trace,"%s contradicts %s because of equation %d\n",
                                  var.name.c_str(),foe.name.c_str(),e+1);
                foe.foes.put(v);
                var.foes.put(k);
                for(int e1 : foe.equations) insert_unique(to_test,e1);
                add_tests(tests,k,var.equations);
                foe.value = Value::Excluded;
              }
            }
            break;
          }
          case Cover::no_free: {
            if(trace) fprintf(trace,"%s is false because of equation %d\n",var.name.c_str(),e+1);
            for(int k : var.foes.ones())
              if(vars[k].value==Value::Excluded) vars[k].value = Value::Free;
            var.value = Value::False;
            queue.push_back(v);
            Status status = eliminate(queue,modified);
            if(status!=Status::open) return status;
            import_modified(modified,tests);
            eliminated = true;
            break;
          }
          case Cover::covered:
            while(!queue.empty()) {
              int k = queue.front();
              queue.pop_front();
              Variable& foe = vars[k];
              if(trace) fprintf(trace,"%s contradicts %s because of equation %d\n",
                                var.name.c_str(),foe.name.c_str(),e+1);
              var.foes.put(k);
              foe.foes.put(v);
              for(int e1 : foe.equations) insert_unique(to_test,e1);
              add_tests(tests,k,var.equations);
              foe.value = Value::Excluded;
            }
        }
      }
      if(!eliminated)
        for(int k : var.foes.ones())
          if(vars[k].value==Value::Excluded) vars[k].value = Value::Free;
    }
    tests.erase(p);
  }
  return Status::open;
}

Status Sat01::light_preprocess() {
  puts("Eliminating assigned variables ...");
  Status status = eliminate_assigned();
  if(status!=Status::open) return status;
  pack();
  return Status::open;
}

Status Sat01::preprocess() {
  puts("Preprocessing ...");
  Status status = eliminate_assigned();
  if(status!=Status::open) return status;
  Tests tests = initial_tests();
  status = propagate(tests);
  if(status!=Status::open) return status;
  pack();
  return Status::open;
}

Status Sat01::assign(int v, Value value) {
  deque<int> queue(1,v), modified;
  vars[v].value = value;
  Status status = eliminate(queue,modified);
  if(status!=Status::open) return status;
  Tests tests;
  import_modified(modified,tests);
  status = propagate(tests);
  if(status!=Status::open) return status;
  pack();
  return Status::open;
}
