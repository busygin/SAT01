/*****************************************************************************
!!  This is the main() function of SAT01 solver                             !!
!!  Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
!! Please email your feedbacks to <busygin@a-teleport.com> and visit        !!
!! Stas Busygin's NP-completeness page: <http://www.busygin.dp.ua/npc.html> !!
*****************************************************************************/

#include <stdio.h>
#include <string.h>
#include <time.h>
#include <exception>
#include <filesystem>
#include <string>

#include "sat01.h"

using namespace std;

int main(int argc,char** argv){
  puts(
    "SAT01 solver, ver. 4.1\n\n"
    "Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.\n\n"
    "This software is distributed AS IS. NO WARRANTY is expressed or implied.\n"
    "The author grants a permission for everyone to use and distribute this\n"
    "software free of charge for research and educational purposes.\n"
  );

  const char* name=nullptr;
  const char* dump_dir=nullptr;
  const char* log_name=nullptr;
  bool text=false;

  for(int a=1;a<argc;++a){
    const char* p=argv[a];
    switch(p[0]){
      case '-':
        switch(p[1]){
          case 't':
            text=false;
            break;
          case 'd':
            dump_dir=p+2;
            break;
          case 'l':
            log_name=p+2;
        }
        break;
      case '+':
        switch(p[1]){
          case 't':
            text=true;
        }
        break;
      default:
        name=p;
    }
  }

  if(!name){
    puts(
      "Syntax: sat01 [+/-t] [-d<dir>] [-l<log_file>] <sat01_file>\n"
      "Flags:\n"
      "+t: input file is text\n"
      "-t: input file is binary (default)\n"
      "-d<dir>: save the instance at every guess to directory <dir>, as\n"
      "         guess<k>_depth<d>.sat01 (binary), for analysis\n"
      "-l<log_file>: log every deduction of propagation to <log_file>\n"
      "sat01_file: SAT01 instance file either text or converted from an NP problem\n"
    );
    return 0;
  }

  Sat01 sat01;
  try{
    if(text)sat01.load_txt(name);
    else sat01.load_bin(name);
  }
  catch(const exception& error){
    printf("ERROR: %s\n",error.what());
    return 1;
  }

  /* FILE* equfile = fopen("klaus.equ","w");
  sat01.print_equations(equfile);
  fclose(equfile); */

  if(dump_dir) filesystem::create_directories(dump_dir);
  FILE* trace=nullptr;
  if(log_name){
    trace=fopen(log_name,"w");
    if(!trace){
      printf("ERROR: cannot open %s\n",log_name);
      return 1;
    }
    sat01.trace=trace;
  }

  string sol_file_name(name);
  size_t ext=sol_file_name.find(".sat01");
  if(ext!=string::npos) sol_file_name.erase(ext);
  sol_file_name+=".out";
  FILE* file=fopen(sol_file_name.c_str(),"w");

  time_t time1,time2;
  time(&time1);
  Status status=sat01.preprocess();
  if(status!=Status::open){
    time(&time2);
    if(status==Status::solved){
      puts("A solution has been found by the propagation.");
      sat01.print_solution(file);
    }else{
      puts("The propagation has revealed that no solution exists.");
      fputs("No solution\n",file);
    }
  }else{
    int depth, max_depth, n_guess;
    bool flag=solve(sat01,depth,max_depth,n_guess,dump_dir);
    time(&time2);
    if(flag){
      printf("A solution has been found at Depth=%d\n",depth);
      sat01.print_solution(file);
    }else{
      puts("No solution.");
      fprintf(file,"No solution.\n\n");
    }
    fprintf(file,
      "%d heuristic guesses and %d backtracks were made\n"
      "Max Depth = %d\n"
      "Expended time = %lg sec.\n",
      n_guess, n_guess-depth, max_depth, difftime(time2,time1)
    );
  }
  fclose(file);
  if(trace) fclose(trace);
  printf("%s: time=%lg sec.\n", name, difftime(time2,time1));

  return 0;
}
