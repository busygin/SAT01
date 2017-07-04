/*****************************************************************************
!!  Factoring->SAT01 converter, ver. 4.0                                    !!
!!  Copyright (c) Stanislav Busygin, 1998-2000. All rights reserved.        !!
!!                                                                          !!
!! This software is distributed AS IS. NO WARRANTY is expressed or implied. !!
!! The author grants a permission for everyone to use and distribute this   !!
!! software free of charge for research and educational purposes.           !!
*****************************************************************************/

#include <stdio.h>
#include <string.h>
#include "bool_vector.h"
#include <vector>
#include <list>
#include "bin_store.h"

using namespace std;

int m,n,h;
int n_var,n_equ;
list<bool> Prod(3,false);

void InitProd(char* p){
  int dig;
  list<bool>::iterator pl1,pl2;
  bool Carry;
  L1:if(*p<'0'||*p>'9')throw(false);
  dig=*p-48;
  pl1=Prod.begin();
  Prod.push_front(dig&1);
  dig>>=1;
  Carry=false;
  while(dig||Carry){
    if(pl1==Prod.end())pl1=Prod.insert(pl1,false);
    bool bit=dig&1;
    bool newbit=*pl1^bit^Carry;
    Carry=(Carry?*pl1||bit:*pl1&&bit);
    *pl1++=newbit;
    dig>>=1;
  }
  if(!*++p)goto L2;
  pl1=Prod.begin();
  pl2=pl1;
  Prod.push_front(*pl2++);
  Prod.insert(++Prod.begin(),*pl2++);
  Carry=false;
  do{
    bool newbit=*pl1^*pl2^Carry;
    Carry=(Carry?*pl1||*pl2:*pl1&&*pl2);
    *pl1++=newbit;
  }while(++pl2!=Prod.end());
  if(Carry){
    Carry=*pl1;
    *pl1=!*pl1;
    if(Carry){
      Carry=*++pl1;
      *pl1=!*pl1;
      if(Carry)Prod.push_back(true);
    }
  }
  goto L1;
  L2:n=Prod.size();
  pl1=--Prod.end();
  while(!*pl1){
    Prod.erase(pl1--);
    if(--n<3)throw(false);
  }
  m=n-1;
  h=(n+1)/2;
}

struct TVar{
  int No;
  char Name[64];
  char f;
  bool_vector foes;
  TVar(int n=0):f(2),foes(n){}
};

int No=0;

vector<TVar*> Vars;

inline void MakeContradictory(TVar& x,TVar& y){
  x.foes.put(y.No);
  y.foes.put(x.No);
}

vector<TVar> x;
vector<TVar> y;
vector< vector<TVar> > xy[2][2];

vector< vector<int> > Equs;

void InitTempBits(){
  x.resize(h,n_var);
  int ii,jj;
  vector<TVar>::iterator j=x.begin();
  for(ii=0;ii<h;++ii,++j){
    j->No=No++;
    sprintf(j->Name,"x%d",ii);
    Vars.push_back(&*j);
  }
  y.resize(m,n_var);
  j=y.begin();
  for(jj=0;jj<m;++jj,++j){
    j->No=No++;
    sprintf(j->Name,"y%d",jj);
    Vars.push_back(&*j);
  }
  int a1,a2,a3;
  for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1)xy[a1][a2].resize(h);
  for(ii=0;ii<h;++ii){
    int len=n-ii;
    if(len>m)len=m;
    for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1)xy[a1][a2][ii].resize(len,n_var);
    for(jj=0;jj<m;++jj)if(jj<len){
      for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1){
        xy[a1][a2][ii][jj].No=No++;
        char* p=xy[a1][a2][ii][jj].Name;
        if(!a1)*p++='~';
        p+=sprintf(p,"x%d&",ii);
        if(!a2)*p++='~';
        sprintf(p,"y%d",jj);
        Vars.push_back(&xy[a1][a2][ii][jj]);
      }

      MakeContradictory(x[ii],xy[0][0][ii][jj]);
      MakeContradictory(y[jj],xy[0][0][ii][jj]);

      MakeContradictory(y[jj],xy[1][0][ii][jj]);

      MakeContradictory(x[ii],xy[0][1][ii][jj]);

      for(int ii1=0;ii1<ii;++ii1)for(a1=0;a1<=1;++a1)for(a2=0;a2<=1;++a2)for(a3=0;a3<=1;++a3)
        MakeContradictory(xy[a1][a3][ii][jj],xy[a2][1-a3][ii1][jj]);
      for(int jj1=0;jj1<jj;++jj1)for(a1=0;a1<=1;++a1)for(a2=0;a2<=1;++a2)for(a3=0;a3<=1;++a3)
        MakeContradictory(xy[a1][a2][ii][jj],xy[1-a1][a3][ii][jj1]);

      MakeContradictory(xy[1][0][ii][jj],xy[0][0][ii][jj]);
      MakeContradictory(xy[0][1][ii][jj],xy[0][0][ii][jj]);
      MakeContradictory(xy[1][1][ii][jj],xy[0][0][ii][jj]);
      MakeContradictory(xy[0][1][ii][jj],xy[1][0][ii][jj]);
      MakeContradictory(xy[1][1][ii][jj],xy[1][0][ii][jj]);
      MakeContradictory(xy[1][1][ii][jj],xy[0][1][ii][jj]);

      Equs.push_back(vector<int>());
      vector< vector<int> >::iterator e=Equs.end()-1;
      e->reserve(3);
      e->push_back(x[ii].No);
      e->push_back(xy[0][0][ii][jj].No);
      e->push_back(xy[0][1][ii][jj].No);

      Equs.push_back(vector<int>());
      e=Equs.end()-1;
      e->reserve(3);
      e->push_back(y[jj].No);
      e->push_back(xy[0][0][ii][jj].No);
      e->push_back(xy[1][0][ii][jj].No);

      Equs.push_back(vector<int>());
      e=Equs.end()-1;
      e->reserve(4);
      for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1)e->push_back(xy[a1][a2][ii][jj].No);
    }else MakeContradictory(x[ii],y[jj]);
  }
  vector<TVar>::iterator i=x.begin()+2;
  for(ii=2;ii<h;++ii,++i){
    j=y.begin()+(m-ii+1);
    for(jj=m-ii+1;jj<m;++jj,++j){
      int jj0=n-ii,ii1,jj1;
      for(a1=0;a1<=1;++a1)for(ii1=0;ii1<n-jj;++ii1){
        MakeContradictory(*i,xy[a1][1][ii1][jj]);
        for(a2=0;a2<=1;++a2)for(jj1=0;jj1<jj0;++jj1)MakeContradictory(xy[1][a2][ii][jj1],xy[a1][1][ii1][jj]);
      }
      for(a2=0;a2<=1;++a2)for(jj1=0;jj1<jj0;++jj1)MakeContradictory(*j,xy[1][a2][ii][jj1]);
    }
  }
  xy[1][1][0][0].f=*Prod.begin();
}

void CompleteCausal(TVar& x,TVar& y){
  vector<TVar*>::iterator jj;
  u_long* vv;
  for(jj=Vars.begin(),vv=y.foes.data;jj<Vars.end();jj+=b_size,++vv){
    u_long mask=*vv;
    vector<TVar*>::iterator jj1=jj;
    while(mask){
      if(mask&1){
        TVar* j=*jj1;
        x.foes.put(j->No);
        j->foes.put(x.No);
      }
      mask>>=1;
      ++jj1;
    }
  }
}

vector< vector<TVar> > s;
vector< vector<TVar> > q;
vector<TVar> l0[2][2];
vector< vector<TVar> > l[2][2][2];

void InitSumBits(){
  s.resize(h-1);
  q.resize(h-1);
  int jj;
  vector<TVar>::iterator j;
  list<bool>::iterator z=++Prod.begin();
  int ii;
  for(ii=0;ii<h-1;++ii,++z){
    s[ii].resize(m-ii-1,n_var);
    jj=ii+1;
    for(j=s[ii].begin();j<s[ii].end();++j,++jj){
      j->No=No++;
      sprintf(j->Name,"s(%d,%d)",ii+1,jj);
      Vars.push_back(&*j);
    }
    s[ii][0].f=*z;
    q[ii].resize(m-ii-1,n_var);
    jj=ii+1;
    for(j=q[ii].begin();j<q[ii].end();++j,++jj){
      j->No=No++;
      sprintf(j->Name,"q(%d,%d)",ii+1,jj);
      Vars.push_back(&*j);
    }
  }
  for(jj=1;jj<=m-h;++jj,++z)s[h-2][jj].f=*z;
  int a1,a2,a3;
  for(a1=0;a1<=1;++a1)for(a2=0;a2<=1;++a2)if(!(a1&&a2))l0[a1][a2].resize(h-1,n_var);
  for(a1=0;a1<=1;++a1)for(a2=0;a2<=1;++a2)for(a3=0;a3<=1;++a3)if(!(a1&&a2&&a3)){
    l[a1][a2][a3].resize(h-1);
    for(ii=0;ii<h-1;++ii)l[a1][a2][a3][ii].resize(m-ii-2,n_var);
  }

  vector< vector<int> >::iterator e;
  for(ii=0;ii<h-1;++ii){
    TVar& s0=(ii?s[ii-1][1]:xy[1][1][0][1]);

    for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1)if(!(a1&&a2)){
      l0[a1][a2][ii].No=No++;
      char* p=l0[a1][a2][ii].Name;
      if(!a1)*p++='~';
      p+=sprintf(p,"%c(%d,%d)&",ii?'s':'b',ii,ii+1);
      if(!a2)*p++='~';
      sprintf(p,"b(%d,%d)",ii+1,ii+1);
      Vars.push_back(&l0[a1][a2][ii]);
    }

    CompleteCausal(l0[1][0][ii],s0);
    CompleteCausal(l0[0][1][ii],xy[1][1][ii+1][0]);
    CompleteCausal(q[ii][0],s0);
    CompleteCausal(q[ii][0],xy[1][1][ii+1][0]);
    MakeContradictory(s0,l0[0][0][ii]);
    MakeContradictory(xy[1][1][ii+1][0],l0[0][0][ii]);
    MakeContradictory(xy[1][1][ii+1][0],l0[1][0][ii]);
    MakeContradictory(s0,l0[0][1][ii]);
    MakeContradictory(l0[0][0][ii],l0[1][0][ii]);
    MakeContradictory(l0[0][0][ii],l0[0][1][ii]);
    MakeContradictory(l0[1][0][ii],l0[0][1][ii]);
    MakeContradictory(s[ii][0],l0[0][0][ii]);
    MakeContradictory(q[ii][0],l0[0][0][ii]);
    MakeContradictory(q[ii][0],l0[1][0][ii]);
    MakeContradictory(q[ii][0],l0[0][1][ii]);
    MakeContradictory(s[ii][0],q[ii][0]);

    Equs.push_back(vector<int>());
    e=Equs.end()-1;
    e->reserve(3);
    e->push_back(s[ii][0].No);
    e->push_back(q[ii][0].No);
    e->push_back(l0[0][0][ii].No);

    Equs.push_back(vector<int>());
    e=Equs.end()-1;
    e->reserve(4);
    e->push_back(q[ii][0].No);
    e->push_back(l0[0][0][ii].No);
    e->push_back(l0[1][0][ii].No);
    e->push_back(l0[0][1][ii].No);

    Equs.push_back(vector<int>());
    e=Equs.end()-1;
    e->reserve(3);
    e->push_back(s0.No);
    e->push_back(l0[0][0][ii].No);
    e->push_back(l0[0][1][ii].No);

    Equs.push_back(vector<int>());
    e=Equs.end()-1;
    e->reserve(3);
    e->push_back(xy[1][1][ii+1][0].No);
    e->push_back(l0[0][0][ii].No);
    e->push_back(l0[1][0][ii].No);

    for(jj=1;jj<m-ii-1;++jj){
      TVar& s1=(ii?s[ii-1][jj+1]:xy[1][1][0][jj+1]);

      for(a3=0;a3<=1;++a3)for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1)if(!(a1&&a2&&a3)){
        l[a1][a2][a3][ii][jj-1].No=No++;
        char* p=l[a1][a2][a3][ii][jj-1].Name;
        if(!a1)*p++='~';
        p+=sprintf(p,"%c(%d,%d)&",ii?'s':'b',ii,ii+jj+1);
        if(!a2)*p++='~';
        p+=sprintf(p,"b(%d,%d)&",ii+1,ii+jj+1);
        if(!a3)*p++='~';
        sprintf(p,"q(%d,%d)",ii,ii+jj);
        Vars.push_back(&l[a1][a2][a3][ii][jj-1]);
      }

      for(a3=0;a3<=1;++a3)for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1)if(!(a1&&a2&&a3)){
        if(a1)CompleteCausal(l[a1][a2][a3][ii][jj-1],s1);
        if(a2)CompleteCausal(l[a1][a2][a3][ii][jj-1],xy[1][1][ii+1][jj]);
        if(a3)CompleteCausal(l[a1][a2][a3][ii][jj-1],q[ii][jj-1]);
      }
      for(a3=0;a3<=1;++a3)for(a2=0;a2<=1;++a2)for(a1=0;a1<=1;++a1)if(!(a1&&a2&&a3)){
        if(!a1)MakeContradictory(l[a1][a2][a3][ii][jj-1],s1);
        if(!a2)MakeContradictory(l[a1][a2][a3][ii][jj-1],xy[1][1][ii+1][jj]);
        if(!a3)MakeContradictory(l[a1][a2][a3][ii][jj-1],q[ii][jj-1]);
        if(a1+a2+a3==1)MakeContradictory(q[ii][jj],l[a1][a2][a3][ii][jj-1]);
        else{
          MakeContradictory(s[ii][jj],l[a1][a2][a3][ii][jj-1]);
          if(!(a1||a2||a3))MakeContradictory(l[a1][a2][a3][ii][jj-1],q[ii][jj]);
        }
      }

      for(int b1=1;b1<7;++b1)for(int b2=0;b2<b1;++b2)
        MakeContradictory(l[b1&1][(b1&2)>>1][(b1&4)>>2][ii][jj-1],l[b2&1][(b2&2)>>1][(b2&4)>>2][ii][jj-1]);

      Equs.push_back(vector<int>());
      e=Equs.end()-1;
      e->reserve(5);
      e->push_back(s1.No);
      e->push_back(l[0][0][0][ii][jj-1].No);
      e->push_back(l[0][1][0][ii][jj-1].No);
      e->push_back(l[0][0][1][ii][jj-1].No);
      e->push_back(l[0][1][1][ii][jj-1].No);

      Equs.push_back(vector<int>());
      e=Equs.end()-1;
      e->reserve(5);
      e->push_back(xy[1][1][ii+1][jj].No);
      e->push_back(l[0][0][0][ii][jj-1].No);
      e->push_back(l[1][0][0][ii][jj-1].No);
      e->push_back(l[0][0][1][ii][jj-1].No);
      e->push_back(l[1][0][1][ii][jj-1].No);

      Equs.push_back(vector<int>());
      e=Equs.end()-1;
      e->reserve(5);
      e->push_back(q[ii][jj-1].No);
      e->push_back(l[0][0][0][ii][jj-1].No);
      e->push_back(l[1][0][0][ii][jj-1].No);
      e->push_back(l[0][1][0][ii][jj-1].No);
      e->push_back(l[1][1][0][ii][jj-1].No);

      Equs.push_back(vector<int>());
      e=Equs.end()-1;
      e->reserve(5);
      e->push_back(s[ii][jj].No);
      e->push_back(l[0][0][0][ii][jj-1].No);
      e->push_back(l[1][1][0][ii][jj-1].No);
      e->push_back(l[1][0][1][ii][jj-1].No);
      e->push_back(l[0][1][1][ii][jj-1].No);

      Equs.push_back(vector<int>());
      e=Equs.end()-1;
      e->reserve(5);
      e->push_back(q[ii][jj].No);
      e->push_back(l[0][0][0][ii][jj-1].No);
      e->push_back(l[1][0][0][ii][jj-1].No);
      e->push_back(l[0][1][0][ii][jj-1].No);
      e->push_back(l[0][0][1][ii][jj-1].No);
    }
  }
  Equs.push_back(vector<int>());
  e=Equs.end()-1;
  e->reserve(2*(h-1));
  for(ii=1;ii<h;++ii){
    e->push_back(xy[1][1][ii][m-ii].No);
    for(jj=0;jj<h-1;++jj)MakeContradictory(xy[1][1][ii][m-ii],q[jj][m-jj-2]);
  }
  for(ii=0;ii<h-1;++ii){
    e->push_back(q[ii][m-ii-2].No);
    for(jj=0;jj<ii;++jj)MakeContradictory(q[ii][m-ii-2],q[jj][m-jj-2]);
  }
}

void Save(char* FName){
  fputs("Storing ...",stdout);
  fflush(stdout);
  FILE* F=fopen(FName,"wb");
  fprintf(F,"!S01_4!");
  write_int(No,F);
  vector<TVar*>::iterator jj;
  TVar* j;
  for(jj=Vars.begin();jj<Vars.end();++jj){
    j=*jj;
    write_int(strlen(j->Name),F);
    fputs(j->Name,F);
    fputc(j->f,F);
  }
  for(jj=Vars.begin();jj<Vars.end();++jj){
    j=*jj;
    fwrite(j->foes.data,sizeof(u_long),j->foes.data_size,F);
  }
  write_int(Equs.size(),F);
  for(vector< vector<int> >::iterator i=Equs.begin();i<Equs.end();++i){
    write_int(i->size(),F);
    for(vector<int>::iterator j=i->begin();j<i->end();++j)write_int(*j,F);
  }
  write_int(0,F);
  fclose(F);
  puts(" done.");
}

int main(int argc,char** argv){
  puts("Factoring to SAT01 converter, ver. 4.0\n\n"
    "Copyright (c) Stanislav Busygin, 1998-2000. All rights reserved.\n\n"
    "This software is distributed AS IS. NO WARRANTY is expressed or implied.\n"
    "The author grants a permission for everyone to use and distribute this\n"
    "software free of charge for research and educational purposes.\n"
  );
  if(argc>=2){
    char* p=*++argv;
    try{
      fputs("Creating SAT01 ...",stdout);
      fflush(stdout);
      InitProd(p);
      n_var=h+5*m+13*(h-1)*(2*m-h)/2;
      n_equ=1+3*m+2*(h-1)*(4*m-2*h+1);
      Vars.reserve(n_var);
      Equs.reserve(n_equ);
      InitTempBits();
      InitSumBits();
      puts(" done.");
      char* FName=new char[strlen(p)+7];
      strcpy(FName,p);
      Save(strcat(FName,".sat01"));
      delete[] FName;
    }
    catch(...){
      puts("\n\nFatal error!");
      return 1;
    }
  }else puts("Syntax: factor2sat01 <number>\n\n"
          "The conversion is correct iff number>3");
  return 0;
}
