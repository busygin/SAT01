/*****************************************************************************
!!  Output files converter for factoring done by SAT01 solver ver. 4.0      !!
!!  Copyright (c) Stanislav Busygin, 1998-2000. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

#include <stdio.h>
#include <string.h>
#include <vector>

using namespace std;

int main(int argc,char** argv){
  puts("Output files converter for factoring\n\n"
    "Copyright (c) Stanislav Busygin, 1998-2000. All rights reserved.\n\n"
    "This software is distributed AS IS. NO WARRANTY is expressed or implied.\n"
    "The author grants a permission for everyone to use and distribute this\n"
    "software free of charge for research and educational purposes.\n"
  );
  if(argc>=2){
    char* s1=*++argv;
    fputs("Converting output file ...",stdout);
    fflush(stdout);
    try{
      FILE* F=fopen(s1,"r");
      char Conj[65536];
      vector<bool> x,y;
      while(fgets(Conj,65535,F))if(Conj[0]=='x'||Conj[0]=='y'){
        char* p=Conj+1;
        int No=0;
        do{No=10*No+*p++-48;}while(*p>='0'&&*p<='9');
        if(Conj[0]=='x'){
          if(x.size()<No+1)x.resize(No+1,false);
          x[No]=true;
        }else{
          if(y.size()<No+1)y.resize(No+1,false);
          y[No]=true;
        }
      }
      fclose(F);
      char* s2=new char[strlen(s1)+7];
      char* p=s2;
      while(*s1&&*s1!='.')*p++=*s1++;
      strcpy(p,".sol");
      F=fopen(s2,"w");
      if(x.empty())fputs("No solution\n",F);
      else{
        vector<bool>::reverse_iterator i;
        unsigned long a=0;
        for(i=x.rbegin();i!=x.rend();++i)a=(a<<1)+(*i);
        unsigned long b=0;
        for(i=y.rbegin();i!=y.rend();++i)b=(b<<1)+(*i);
        fprintf(F,"%ld*%ld=%ld\n",a,b,a*b);
      }
      fclose(F);
      delete[] s2;
      puts(" done.");
    }
    catch(...){
      puts("\n\nFatal error!");
      return 1;
    }
  }else puts("Syntax: factor_out2sol <out_file>\n\n"
          "<out_file> must be an output file of SAT01 solver.");
  return 0;
}
