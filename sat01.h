#ifndef SAT01_H
#define SAT01_H

#include <stdio.h>
#include "bool_vector.h"
#include <vector>
#include <list>
#include <map>
#include <functional>

using namespace std;

struct Var;

struct Equ:public vector<Var*> {
  int n;
  bool sat,mod;
  Equ(int _n=0):vector<Var*>(_n),n(_n),sat(false),mod(false){}

  void print(FILE* file);
};

struct Var{
  char* name;
  bool_vector foes;
  vector<Equ*> equs;
  char f;
  bool flag;
  Var(int n=0):name(NULL),foes(n),f(2),flag(false){}
  ~Var(){if(name)delete[] name;}
  void reduce(vector<Var>& vars,list<Var*>& q,list<Equ*>& modified);
};

typedef map< Var*,vector<Equ*> > VEMap;
typedef vector<double> RealVector;

struct Equation:public unary_function<double,double>{
  int n;
  double* a;
  double* b;
  double rhs;
  Equation():a(NULL){}
  ~Equation(){if(a)delete[] a;}
  double operator()(const double x);
};

struct Sat01 {
  int n;
  vector<Var> vars;
  vector<Equ> equs;
  vector<char*> ones;

  Sat01(): n(0) {}
  ~Sat01() {
    vector<char*>::iterator jj;
    for(jj=ones.begin();jj<ones.end();++jj) delete[] *jj;
  }

  void reduce(list<Var*>& q, list<Equ*>& modified) {
    while(!q.empty()){
      q.front()->reduce(vars,q,modified);
      --n;
      q.pop_front();
    }
    if(!n)throw(true);
  }
  void import_modif(list<Equ*>& modified, VEMap& ve);
  void propagate(VEMap& ve);
  void pack();

  void light_preprocess();

  void preprocess();

  void var_in_equ(int var_no, Equ* equ);

  void load_bin(const char* f_name);
  void load_txt(const char* f_name);
  void save_bin(const char* f_name);
  void save_txt(const char* f_name);

  void print_solution(FILE* file);

  void print_equations(FILE* file) {
    for(vector<Equ>::iterator p=equs.begin();p<equs.end();++p) p->print(file);
  }
};

bool solve(Sat01*& sat01, int& depth, int& max_depth, int& n_guess);

#endif
