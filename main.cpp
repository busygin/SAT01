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

#include "sat01.h"

int main(int argc,char** argv){
  puts(
    "SAT01 solver, ver. 4.1\n\n"
    "Copyright (c) Stanislav Busygin, 1998-2017. All rights reserved.\n\n"
    "This software is distributed AS IS. NO WARRANTY is expressed or implied.\n"
    "The author grants a permission for everyone to use and distribute this\n"
    "software free of charge for research and educational purposes.\n"
  );

  char* name=NULL;
  bool text=false;
  char* p;

  while(argc-->=2){
    p=*++argv;
    switch(p[0]){
      case '-':
        switch(p[1]){
          case 't':
            text=false;
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

  if(name){
    Sat01* sat01=new Sat01;
    if(text)sat01->load_txt(name);
    else sat01->load_bin(name);

    /* FILE* equfile = fopen("klaus.equ","w");
    sat01->print_equations(equfile);
    fclose(equfile); */

    int i=strlen(name);
    char* sol_file_name=new char[i+7];
    memcpy(sol_file_name,name,i+1);
    char* p=strstr(sol_file_name,".sat01");
    if(!p)p=sol_file_name+i;
    strcpy(p,".out");
    FILE* file=fopen(sol_file_name,"w");
    delete[] sol_file_name;

    int depth, max_depth, n_guess;
    time_t time1,time2;
    double dt;
    bool flag;
    time(&time1);
    try{sat01->preprocess();}
    catch(bool result){
      time(&time2);
      dt = difftime(time2,time1);
      if(result){
        puts("A solution has been found by the propagation.");
        sat01->print_solution(file);
      }else{
        puts("The propagation has revealed that no solution exists.");
        fputs("No solution\n",file);
      }
      goto L1;
    }
    flag = solve(sat01,depth,max_depth,n_guess);
    time(&time2);
    dt = difftime(time2,time1);
    if(flag){
      printf("A solution has been found at Depth=%d\n",depth);
      sat01->print_solution(file);
    }else{
      puts("No solution.");
      fprintf(file,"No solution.\n\n");
    }
    fprintf(file,
      "%d heuristic guesses and %d backtracks were made\n"
      "Max Depth = %d\n"
      "Expended time = %lg sec.\n",
      n_guess, n_guess-depth, max_depth, dt
    );
    L1:fclose(file);
    delete sat01;
    printf("%s: time=%lg sec.\n", name, dt);
  }else puts (
    "Syntax: sat01 [+/-t] <sat01_file>\n"
    "Flags:\n"
    "+t: input file is text\n"
    "-t: input file is binary (default)\n"
    "sat01_file: SAT01 instance file either text or converted from an NP problem\n"
  );

  return 0;
}
