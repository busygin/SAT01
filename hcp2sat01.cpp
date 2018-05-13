/*****************************************************************************
!!  Hamilton Cycle Problem->SAT01 converter, ver. 2.0                       !!
!!  Copyright (c) Stanislav Busygin, 1998-2018. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

#include <cstdio>
#include "bool_vector.h"
#include <vector>
#include "bin_store.h"

using namespace std;

struct TVar{
  char Name[16];
  char f;
  bool_vector foes;
  TVar(int n=0):f(2),foes(n){}
};

vector<TVar> Vars;

int n=0,v0=0;

void MakeContradictory(int i,int j){
  Vars[i].foes.put(j);
  Vars[j].foes.put(i);
}

void InitVars(){
  int m=n*n;
  Vars.resize(m,m);
  for(int i=0;i<n;++i){
    int j=(i+1)%n;
    for(int k=0;k<n;++k){
      sprintf(Vars[i*n+k].Name,"x(%d,%d)",i,k);
      for(int l=0;l<k;++l){
        MakeContradictory(i*n+k,j*n+l);
        MakeContradictory(i*n+l,j*n+k);
      }
    }
    for(j=1;j<n;++j)for(int k=0;k<j;++k){
      MakeContradictory(i*n+j,i*n+k);
      MakeContradictory(j*n+i,k*n+i);
    }
  }
}

void MakeFriends(int i,int j){
  Vars[i].foes.clear(j);
  Vars[j].foes.clear(i);
}

void MakeArc(int i,int j){
  for(int t=0;t<n;++t){
    int t1=(t+1)%n;
    MakeFriends(t*n+i,t1*n+j);
  }
}

void GetLex(FILE* F,char* str){
  char* p=str;
  int c;
  do{c=getc(F);}while(((c!=EOF)&&(c<=' '))||(c==':'));
  if(c==EOF){
    printf("\nERROR: Unexpected end of file\n");
    fclose(F);
    throw(false);
  }
  do{
    if((c>='a')&&(c<='z'))c-='a'-'A';
    *p++=c;
    c=fgetc(F);
  }while(!((c<=' ')||(c==':')));
  *p=0;
}

void Load(char* FName){
  fputs("Loading ...",stdout);
	FILE* F=fopen(FName,"rb");
  if(!F){
    printf("\nERROR: Unable to read from file %s\n",FName);
    throw(false);
  }
  bool Type=false,isList=true,isText=true,isDirected=false;
  char str1[1024],str2[1024];
  int u,v;
  L1:GetLex(F,str1);
  if(!strcmp(str1,"EDGE_DATA_SECTION")){
    if(!Type){
      printf("\nERROR: Incorrect type of problem\n");
      fclose(F);
      throw(false);
    }
    if(Vars.empty()){
      printf("\nERROR: Unable to determine dimension of the problem\n");
      fclose(F);
      throw(false);
    }
    if(isList){
      if(isText){
        L2:fscanf(F,"%d",&u);
        if(u==-1)goto L4;
        fscanf(F,"%d",&v);
        MakeArc(u-1,v-1);
        if(!isDirected)MakeArc(v-1,u-1);
        goto L2;
      }else{
        L3:fread(&u,sizeof(int),1,F);
        if(u==-1)goto L4;
        fread(&v,sizeof(int),1,F);
        MakeArc(u,v);
        if(!isDirected)MakeArc(v,u);
        goto L3;
      }
    }else{
      if(isText){
        for(u=!isDirected;u<n;u++)for(v=0;v<(isDirected?n:u);v++){
          int b;
          fscanf(F,"%d",&b);
          if(b){
            MakeArc(u,v);
            if(!isDirected)MakeArc(v,u);
          }
        }
      }else{
        for(u=0;u<n;u++){
          v=0;
          for(int byte=0;byte<=(isDirected?n:u)/8;byte++){
            char c;
            fread(&c,1,1,F);
            char mask=128;
            for(int bit=0;bit<8&&v<(isDirected?n:u);bit++){
              if(c&mask){
                MakeArc(u,v);
                if(!isDirected)MakeArc(v,u);
              }
              mask=mask>>1;
              v++;
            }
          }
        }
      }
      goto L4;
    }
  }
  GetLex(F,str2);
  if(!strcmp(str1,"TYPE")){
    if(strcmp(str2,"HCP")){
      printf("\nERROR: Incorrect type of problem\n");
      fclose(F);
      throw(false);
    }else Type=true;
  }else if(!strcmp(str1,"EDGE_DATA_FORMAT")){
    if(strcmp(str2,"EDGE_LIST")){
      if(strcmp(str2,"FULL_MATRIX")){
        printf("\nERROR: Unknown type of EDGE_DATA_FORMAT\n");
        fclose(F);
        throw(false);
      }else isList=false;
    }
  }else if(!strcmp(str1,"FORMAT")){
    if(strcmp(str2,"TEXT")){
      if(strcmp(str2,"BINARY")){
        printf("\nERROR: Unknown type of storing format\n");
        fclose(F);
        throw(false);
      }else isText=false;
    }
  }else if(!strcmp(str1,"DIRECTED")){
    if(strcmp(str2,"FALSE")){
      if(strcmp(str2,"TRUE")){
        printf("\nERROR: Incorrect DIRECTED parameter\n");
        fclose(F);
        throw(false);
      }else isDirected=true;
    }
  }else if(!(strcmp(str1,"DIMENSION")&&strcmp(str1,"SIZE"))){
    n=atoi(str2);
    if(n<2){
      printf("\nERROR: Incorrect DIMENSION parameter\n");
      fclose(F);
      throw(false);
    }
    InitVars();
  }else if(!strcmp(str1,"STARTING_VERTEX")){
    v0=atoi(str2)-1;
    if(v0<0){
      printf("\nERROR: Incorrect STARTING_VERTEX parameter\n");
      fclose(F);
      throw(false);
    }
  }
  goto L1;
  L4:fclose(F);
  Vars[v0].f=1;
  puts(" done.");
}

void Save(char* FName){
  fputs("Storing ...",stdout);
  fflush(stdout);
  FILE* F=fopen(FName,"wb");
  fprintf(F,"!S01_4!");
  write_int(n*n,F);
  vector<TVar>::iterator j;
  for(j=Vars.begin();j<Vars.end();++j){
    write_int(strlen(j->Name),F);
    fputs(j->Name,F);
    fputc(j->f,F);
  }
  for(j=Vars.begin();j<Vars.end();++j)fwrite(j->foes.data,sizeof(u_long),j->foes.data_size,F);
  write_int(2*n,F);
  for(int i=0;i<n;++i){
    write_int(n,F);
    for(int j=0;j<n;++j)write_int(i*n+j,F);
  }
  for(int i=0;i<n;++i){
    write_int(n,F);
    for(int j=0;j<n;++j)write_int(j*n+i,F);
  }
  write_int(0,F);
  fclose(F);
  puts(" done.");
}

int main(int argc,char* argv[]){
  puts("Hamilton Cycle Problem to SAT01 converter, ver. 2.0\n\n"
    "Copyright (c) Stanislav Busygin, 1998-2018. All rights reserved.\n\n"
    "This software is distributed AS IS. NO WARRANTY is expressed or implied.\n"
    "The author grants a permission for everyone to use and distribute this\n"
    "software free of charge for research and educational purposes.\n"
  );
  if(argc>=2){
    char* s1=*++argv;
    try{
      Load(s1);
      char* s2=new char[strlen(s1)+7];
      char* p=s2;
      while(*s1&&*s1!='.')*p++=*s1++;
      strcpy(p,".sat01");
      Save(s2);
      delete[] s2;
    }
    catch(...){
      printf("\n\nFatal error!\n");
      return 1;
    }
  }else printf("Syntax: hcp2sat01 <hcp_file>\n\n"
          "Input file must be in an extended TSPLIB hcp format.\n");
  return 0;
}
