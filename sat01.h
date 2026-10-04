/*****************************************************************************
!!  SAT01 solver: the instance and its propagation                          !!
!!  Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

// SAT01 asks for x in {0,1}^n such that every equation sum_{j in e} x_j = 1
// holds and x_i x_j = 0 for every contradiction (i,j); any two variables of an
// equation contradict each other.  Equations and variables refer to each
// other by their indices, so that a state of the solver is an ordinary value
// that can be copied.

#ifndef SAT01_H
#define SAT01_H

#include <stdio.h>
#include <algorithm>
#include <deque>
#include <map>
#include <string>
#include <vector>

#include "bool_vector.h"

// the value of a variable.  Excluded is a free variable that the contradiction
// analysis of a variable it contradicts treats as false, since that analysis
// assumes the variable true.  The numbers are those of the instance files.
enum class Value : char { False = 0, True = 1, Free = 2, Excluded = 3 };

struct Variable {
  std::string name;            // twins merged by pack() have their names joined by '\n'
  bool_vector foes;            // the variables this one contradicts
  std::vector<int> equations;  // the equations it is in, ascending
  Value value = Value::Free;
  bool flag = false;           // a scratch mark of import_modified()

  Variable() = default;
  explicit Variable(int n): foes(n) {}
};

struct Equation {
  std::vector<int> vars;   // its variables, ascending
  int unassigned = 0;      // its variables not eliminated yet
  bool satisfied = false;  // one of its variables has been eliminated as true
  bool modified = false;   // it is queued for the covering analysis
};

// the outcome of propagation: the instance is still open, solved (every
// variable is assigned), or has a contradiction
enum class Status { open, solved, contradiction };

// what find_covering_vars() finds in an equation
enum class Cover {
  no_free,   // no free variable: the equation cannot hold
  one_free,  // a single free variable, which must be true
  covered    // two or more; the variables covering them all are reported
};

// the contradiction tests to make: each free variable maps to the equations
// its contradiction analysis is to examine, both ascending
typedef std::map<int, std::vector<int>> Tests;

class Sat01 {
public:
  int n_unassigned = 0;           // the variables not eliminated yet
  std::vector<Variable> vars;
  std::vector<Equation> equs;
  std::vector<std::string> ones;  // the names of the true variables pack() has removed
  FILE* trace = nullptr;          // where each deduction is reported, if anywhere

  // input and output (sat01_io.cpp)
  void load_bin(const char* file_name);
  void load_txt(const char* file_name);
  void save_bin(const char* file_name) const;
  void save_txt(const char* file_name) const;
  void print_solution(FILE* file) const;
  void print_equations(FILE* file) const;

  // preprocessing (propagation.cpp).  light_preprocess() eliminates the
  // assigned variables with unit propagation and the covering (clique)
  // analysis, and preprocess() adds the contradiction analysis; both end
  // with pack().
  Status light_preprocess();
  Status preprocess();

  // assign() makes a free variable true, or false, and propagates the
  // consequences with all three analyses, ending with pack() (propagation.cpp)
  Status assign(int v, Value value);

  // pack() removes the assigned variables, merges twins, variables with the
  // same contradictions, and drops duplicate equations (pack.cpp)
  void pack();

private:
  void add_to_equation(int v, int e);

  void remove_variable(int v);
  bool twins(int v, int u) const;
  void merge_twin(int v, int u);

  Status eliminate(std::deque<int>& queue, std::deque<int>& modified);
  Status eliminate_one(int v, std::deque<int>& queue, std::deque<int>& modified);
  Cover find_covering_vars(int e, int& single, std::deque<int>& coverings);
  Status cover(int e, std::deque<int>& queue, std::deque<int>& modified);
  Status cover_modified(std::deque<int>& queue, std::deque<int>& modified);
  void import_modified(std::deque<int>& modified, Tests& tests);
  Status propagate(Tests& tests);
  Status eliminate_assigned();
  Tests initial_tests();
};

// solve() searches for a solution, guessing a variable true and backtracking
// to its negation, with every guess propagated by assign().  On success the
// solution is in sat01.  dump_dir, unless null, receives the instance at every
// guess, before the guess, as guess<k>_depth<d>.sat01 in the binary format
// (k counting the guesses from 1, d the number of guesses it rests on).
bool solve(Sat01& sat01, int& depth, int& max_depth, int& n_guess,
           const char* dump_dir);

// sorted vectors of indices
inline void insert_sorted(std::vector<int>& a, int x) {
  a.insert(std::lower_bound(a.begin(),a.end(),x),x);
}

inline void insert_unique(std::vector<int>& a, int x) {
  std::vector<int>::iterator p = std::lower_bound(a.begin(),a.end(),x);
  if(p==a.end() || *p!=x) a.insert(p,x);
}

inline void erase_sorted(std::vector<int>& a, int x) {
  a.erase(std::lower_bound(a.begin(),a.end(),x));
}

#endif
