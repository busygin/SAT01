/*****************************************************************************
!!  SAT01 solver: input and output of instances                             !!
!!  Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

// The binary format (signature !S01_4!) holds, in 32-bit little-endian
// integers: the number of variables n; for each variable the length of its
// name, the name and its value as one byte; the foes of each variable as the
// 64-bit words of a bit string of length n; the number of equations, and for
// each its size and its variables; the number of true variables already
// removed and the length and name of each.
//
// The text format is a line "p SAT01 <n> <m> <c>", then m lines
// "e <variables> 0" and c lines "c <variable> <variable>", the variables
// numbered from 1.

#include <string.h>
#include <stdexcept>

#include "bin_store.h"
#include "sat01.h"

using namespace std;

static FILE* open_file(const char* file_name, const char* mode) {
  FILE* file = fopen(file_name,mode);
  if(!file) throw runtime_error(string("cannot open ")+file_name);
  return file;
}

static void read_bytes(void* data, size_t size, FILE* file) {
  if(size && fread(data,1,size,file)!=size) throw runtime_error("truncated SAT01 file");
}

static string read_name(FILE* file) {
  string name(read_int(file),'\0');
  read_bytes(&name[0],name.size(),file);
  return name;
}

static void write_name(const string& name, FILE* file) {
  write_int((int)name.size(),file);
  fwrite(name.data(),1,name.size(),file);
}

void Sat01::load_bin(const char* file_name) {
  FILE* file = open_file(file_name,"rb");
  char sign[8] = {0};
  read_bytes(sign,7,file);
  if(strcmp(sign,"!S01_4!")) {
    fclose(file);
    throw runtime_error(string(file_name)+" is not a SAT01 file");
  }
  int n = read_int(file);
  n_unassigned = n;
  vars.assign(n,Variable(n));
  for(Variable& var : vars) {
    var.name = read_name(file);
    var.value = Value(fgetc(file));
  }
  for(Variable& var : vars)
    read_bytes(var.foes.words(),sizeof(bool_vector::word)*var.foes.n_words(),file);
  int m = read_int(file);
  equs.assign(m,Equation());
  for(int e=0;e<m;++e) {
    Equation& equ = equs[e];
    equ.vars.resize(read_int(file));
    equ.unassigned = (int)equ.vars.size();
    for(int& v : equ.vars) {
      v = read_int(file);
      vars[v].equations.push_back(e);
    }
  }
  ones.resize(read_int(file));
  for(string& name : ones) name = read_name(file);
  fclose(file);
  printf("%d variables, %d equations\n",n,m);
}

void Sat01::save_bin(const char* file_name) const {
  FILE* file = open_file(file_name,"wb");
  fputs("!S01_4!",file);
  write_int((int)vars.size(),file);
  for(const Variable& var : vars) {
    write_name(var.name,file);
    fputc((char)var.value,file);
  }
  for(const Variable& var : vars)
    fwrite(var.foes.words(),sizeof(bool_vector::word),var.foes.n_words(),file);
  write_int((int)equs.size(),file);
  for(const Equation& equ : equs) {
    write_int((int)equ.vars.size(),file);
    for(int v : equ.vars) write_int(v,file);
  }
  write_int((int)ones.size(),file);
  for(const string& name : ones) write_name(name,file);
  fclose(file);
}

// add_to_equation() puts variable v into equation e, which makes it a foe of
// every variable already there
void Sat01::add_to_equation(int v, int e) {
  Equation& equ = equs[e];
  for(int u : equ.vars) {
    vars[v].foes.put(u);
    vars[u].foes.put(v);
  }
  insert_sorted(equ.vars,v);
  insert_sorted(vars[v].equations,e);
  ++equ.unassigned;
}

void Sat01::load_txt(const char* file_name) {
  FILE* file = open_file(file_name,"r");
  char tag[16];
  int n, m, n_contradictions;
  if(fscanf(file," p %15s %d %d %d",tag,&n,&m,&n_contradictions)!=4 || strcmp(tag,"SAT01")) {
    fclose(file);
    throw runtime_error(string(file_name)+" is not a SAT01 text file");
  }
  n_unassigned = n;
  vars.assign(n,Variable(n));
  for(int v=0;v<n;++v) vars[v].name = "x"+to_string(v+1);
  equs.assign(m,Equation());
  int e = 0;
  for(int line=0;line<m+n_contradictions;++line) {
    char c;
    int v, u;
    if(fscanf(file," %c",&c)!=1) throw runtime_error("truncated SAT01 text file");
    switch(c) {
      case 'e':
        while(fscanf(file,"%d",&v)==1 && v) add_to_equation(v-1,e);
        ++e;
        break;
      case 'c':
        if(fscanf(file,"%d %d",&v,&u)!=2) throw runtime_error("bad contradiction line");
        vars[v-1].foes.put(u-1);
        vars[u-1].foes.put(v-1);
        break;
      default:
        fclose(file);
        throw runtime_error(string("unexpected line in ")+file_name);
    }
  }
  fclose(file);
  printf("%d variables, %d equations\n",n,(int)equs.size());
}

void Sat01::save_txt(const char* file_name) const {
  FILE* file = open_file(file_name,"w");
  int n = (int)vars.size(), n_contradictions = 0;
  for(int v=1;v<n;++v)
    for(int u : vars[v].foes.ones()) {
      if(u>=v) break;
      ++n_contradictions;
    }
  fprintf(file,"p SAT01 %d %d %d\n",n,(int)equs.size(),n_contradictions);
  for(const Equation& equ : equs) {
    fputs("e ",file);
    for(int v : equ.vars) fprintf(file,"%d ",v+1);
    fputs("0\n",file);
  }
  for(int v=1;v<n;++v)
    for(int u : vars[v].foes.ones()) {
      if(u>=v) break;
      fprintf(file,"c %d %d\n",v+1,u+1);
    }
  fclose(file);
}

void Sat01::print_solution(FILE* file) const {
  fputs("True variables of the found solution:\n",file);
  for(const string& name : ones) {
    fputs(name.c_str(),file);
    fputc('\n',file);
  }
  for(const Variable& var : vars)
    if(var.value==Value::True) {
      fputs(var.name.c_str(),file);
      fputc('\n',file);
    }
}

void Sat01::print_equations(FILE* file) const {
  for(const Equation& equ : equs) {
    for(size_t t=0;t<equ.vars.size();++t)
      fprintf(file,t ? "+(%s)" : "(%s)",vars[equ.vars[t]].name.c_str());
    fputs("=1\n",file);
  }
}
