#include <string.h>

#include <algorithm>

#include "sat01.h"
#include "bin_store.h"

#define VEC_INS(A,x) A.insert(lower_bound(A.begin(),A.end(),x),x)
#define VEC_DEL(A,x) A.erase(lower_bound(A.begin(),A.end(),x))

// FILE* trace = fopen("klaus.trc","w");

void Equ::print(FILE* file) {
  iterator p=begin();
  fprintf(file,"(%s)",(*p)->name);
  for(++p;p<end();++p) fprintf(file,"+(%s)",(*p)->name);
  fputs("=1\n",file);
}

void Var::reduce(vector<Var>& vars,list<Var*>& q,list<Equ*>& modified){
  vector<Var>::iterator j, j1;
  u_long* jj;
  u_long v;
  vector<Equ*>::iterator ii;
  Equ* i;
  if(f){
    for(j=vars.begin(),jj=foes.data;j<vars.end();j+=b_size,++jj){
      v=*jj;
      j1=j;
      while(v){
        if(v&1){
          switch(j1->f){
            case 1:throw(false);
            case 2:

              // fprintf(trace,"%s is false by unit propagation\n",j1->name);

              j1->f=0;
              q.push_back(&*j1);
          }
        }
        v>>=1;
        ++j1;
      }
    }
    for(ii=equs.begin();ii<equs.end();++ii){
      i=*ii;
      --i->n;
      i->sat=true;
    }
  }else{
    for(ii=equs.begin();ii<equs.end();++ii){
      i=*ii;
      --i->n;
      if(!i->sat){
        vector<Var*>::iterator jj;
        switch(i->n){
          case 0:throw(false);
          case 1:
            for(jj=i->begin();jj<i->end();++jj){
              Var* j=*jj;
              if(j->f){
                if(j->f==2){

                  // fprintf(trace,"%s is true by unit propagation\n",j->name);

                  j->f=1;
                  q.push_back(j);
                }
                goto L1;
              }
            }
          default:
            if(!i->mod){
              i->mod=true;
              modified.push_back(i);
            }
        }
        L1:;
      }
    }
  }
}

void find_covering_vars(vector<Var>& vars,vector<Var*>& covered,list<Var*>& coverings){
  vector<bool_vector*> c;
  c.reserve(covered.size());
  Var* v=NULL;
  vector<Var*>::iterator jj;
  for(jj=covered.begin();jj<covered.end();++jj){
    Var* j=*jj;
    if(j->f==2){
      v=j;
      c.push_back(&j->foes);
    }
  }
  if(!v)throw(int(0));
  int size=c.size();
  if(size==1)throw(v);
  vector<Var>::iterator j, j1;
  vector<bool_vector*>::iterator pp;
  u_long mask;
  int i=0;
  for(j=vars.begin();j<vars.end();j+=b_size,++i) {
    mask = *((*c.begin())->data+i);
    if(!mask) goto L1;
    for(pp=c.begin()+1;pp<c.end();++pp){
      if(!(mask&=*((*pp)->data+i))) goto L1;
    }
    j1=j;
    do {
      if((mask&1) && j1->f==2) coverings.push_back(&*j1);
      mask>>=1;
      ++j1;
    } while(mask);
    L1:;
  }
}

void Sat01::import_modif(list<Equ*>& modified,VEMap& ve) {
  int count[64];
  while(!modified.empty()){
    Equ* i=modified.front();
    modified.pop_front();
    i->mod=false;
    if(i->n){
      vector<bool_vector*> c;
      c.reserve(i->n);
      vector<Var*>::iterator jj;
      for(jj=i->begin();jj<i->end();++jj) {
        Var* j=*jj;
        if(j->f==2) {
	  c.push_back(&j->foes);
	  j->flag=true;
	}
      }
      vector<Var>::iterator j1;
      int k=0;
      for(j1=vars.begin();j1<vars.end();j1+=b_size,++k) {
        memset(count,0,b_size*sizeof(int));
	for(vector<bool_vector*>::iterator pp=c.begin();pp<c.end();++pp) {
          u_long v = *((*pp)->data+k);
	  int* pc=count;
	  while(v) {
	    if(v&1) ++(*pc);
	    v>>=1;
	    ++pc;
	  }
	}
	for(unsigned int k1=0;k1<b_size;++k1) if(2*(*(count+k1)) >= i->n) {
	  Var* j = &*(j1+k1);
	  if(!j->flag) {
            VEMap::iterator p=ve.lower_bound(j);
            if(p==ve.end()||p->first!=j)p=ve.insert(p,VEMap::value_type(j,vector<Equ*>()));
            vector<Equ*>& c_equs=p->second;
            vector<Equ*>::iterator ii1=lower_bound(c_equs.begin(),c_equs.end(),i);
            if(ii1==c_equs.end()||*ii1!=i)c_equs.insert(ii1,i);
	  } else j->flag=false;
	}
      }
    }
  }
}

void Sat01::propagate(VEMap& ve){
  list<Var*> q;
  list<Equ*> modified;
  u_long* jj;
  u_long* jj1;
  u_long v;
  while(!ve.empty()){
    VEMap::iterator p=ve.begin();
    Var* j=p->first;
    vector<Var>::iterator j1, j2, j3;
    if(j->f==2){
      for(j1=vars.begin(),jj=j->foes.data;j1<vars.end();j1+=b_size,++jj){ //all foes of j must be 3
        v=*jj;
        j2=j1;
        while(v){
          if((v&1)&&j2->f==2)j2->f=3;
          v>>=1;
          ++j2;
        }
      }
      int nj = j - &*(vars.begin());
      vector<Equ*>& c_equs=p->second;
      while(!c_equs.empty()){
        vector<Equ*>::iterator ii=c_equs.end()-1;
        Equ* i=*ii;
        c_equs.erase(ii);
        if(i->n){
          try{find_covering_vars(vars,*i,q);}
          catch(Var* j1){
            //the goal of this code is to provide j with foes of j1 that are new for it
            u_long mask;
            j2=vars.begin();
            for(jj=j->foes.data,jj1=j1->foes.data;
            jj<j->foes.data+j->foes.data_size;
            ++jj,++jj1,j2+=b_size){
              mask=(*jj1)&~(*jj); //mask of new foes of j
              j3=j2;
              u_long mask1=0,b=1;
              while(mask){
                if((mask&1)&&j3->f==2){

                  // fprintf(trace,"%s contradicts %s because of equation %d\n",j->name,j3->name,i-&equs[0]+1);

                  j3->foes.put(nj); //j3 is a new foe of j
                  vector<Equ*>::iterator ii1;
                  for(ii1=j3->equs.begin();ii1<j3->equs.end();++ii1){ //update c_equs by new equations (with j3)
                    Equ* i1=*ii1;
                    vector<Equ*>::iterator ii2=lower_bound(c_equs.begin(),c_equs.end(),i1);
                    if(ii2==c_equs.end()||*ii2!=i1)c_equs.insert(ii2,i1);
                  }
                  VEMap::iterator p2=ve.lower_bound(&*j3); //update to-be-tested equs for j3 with j->equs
                  if(p2==ve.end()||p2->first!=&*j3)ve.insert(p2,VEMap::value_type(&*j3,j->equs));
                  else{
                    vector<Equ*>& c_equs2=p2->second;
                    for(ii1=j->equs.begin();ii1<j->equs.end();++ii1){
                      Equ* i1=*ii1;
                      vector<Equ*>::iterator ii2=lower_bound(c_equs2.begin(),c_equs2.end(),i1);
                      if(ii2==c_equs2.end()||*ii2!=i1)c_equs2.insert(ii2,i1);
                    }
                  }
                  j3->f=3; //as a foe of the currently tested var j3 must be 3
                  mask1|=b;
                }
                b<<=1;
                mask>>=1;
                ++j3;
              }
              (*jj)|=(*jj1)&mask1; //update foes of j
            }
            goto L1;
          }
          catch(...){

            // fprintf(trace,"%s is false because of equation %d\n",j->name,i-&equs[0]+1);

            //j must be 0
            for(j1=vars.begin(),jj=j->foes.data;j1<vars.end();j1+=b_size,++jj){ //all foes of j must be 3
              v=*jj;
              j2=j1;
              while(v){
                if((v&1)&&j2->f==3)j2->f=2;
                v>>=1;
                ++j2;
              }
            }
            j->f=0;
            q.push_back(j);
            reduce(q,modified);
            import_modif(modified,ve);
            goto L2;
          }
          while(!q.empty()){
            Var* j1=q.front(); //j1 is to be foe of j

            // fprintf(trace,"%s contradicts %s because of equation %d\n",j->name,j1->name,i-&equs[0]+1);

            q.pop_front();
            j->foes.put(j1 - &*(vars.begin())); //j1 is a new foe of j
            j1->foes.put(nj);
            vector<Equ*>::iterator ii1;
            for(ii1=j1->equs.begin();ii1<j1->equs.end();++ii1){ //update c_equs by new equations (with j1)
              Equ* i1=*ii1;
              vector<Equ*>::iterator ii2=lower_bound(c_equs.begin(),c_equs.end(),i1);
              if(ii2==c_equs.end()||*ii2!=i1)c_equs.insert(ii2,i1);
            }
            VEMap::iterator p2=ve.lower_bound(j1); //update to-be-tested equs for j1 with j->equs
            if(p2==ve.end()||p2->first!=j1)ve.insert(p2,VEMap::value_type(j1,j->equs));
            else{
              vector<Equ*>& c_equs2=p2->second;
              for(ii1=j->equs.begin();ii1<j->equs.end();++ii1){
                Equ* i1=*ii1;
                vector<Equ*>::iterator ii2=lower_bound(c_equs2.begin(),c_equs2.end(),i1);
                if(ii2==c_equs2.end()||*ii2!=i1)c_equs2.insert(ii2,i1);
              }
            }
            j1->f=3; //as a foe of the currently tested var j1 must be 3
          }
          L1:;
        }
      }
      for(j1=vars.begin(),jj=j->foes.data;j1<vars.end();j1+=b_size,++jj){ //restore foes of j
        v=*jj;
        j2=j1;
        while(v){
          if((v&1)&&j2->f==3)j2->f=2;
          v>>=1;
          ++j2;
        }
      }
      L2:;
    }
    ve.erase(p);
  }

  // fclose(trace);
}

void Sat01::pack(){
  vector<Var*> p_vars;
  p_vars.reserve(n);
  vector<Var>::iterator j, j1;
  int no=vars.size()-1;
  for(j=vars.end()-1;no>=0;--j,--no)switch(j->f){
    case 1:
      ones.push_back(j->name);
      goto L2;
    case 2:
      for(j1=vars.begin();j1<j;++j1)if(j1->f==2){
        u_long* v=j->foes.data;
        u_long* last_v=v+j->foes.data_size;
        u_long* v1=j1->foes.data;
        for(vector<Var>::iterator j2=vars.begin();v<last_v;j2+=b_size,++v,++v1){
          u_long mask=(*v)^(*v1);
          vector<Var>::iterator j3=j2;
          while(mask){
            if((mask&1)&&(j3>=j||j3->f==2))goto L1;
            mask>>=1;
            ++j3;
          }
        }
        {int l=strlen(j->name);
        char* p=new char[l+strlen(j1->name)+2];
        strcpy(p,j->name);
        p[l]='\n';
        strcpy(p+(l+1),j1->name);
        delete[] j->name;
        j->name=p;
        j1->f=0;
        for(vector<Equ*>::iterator ii=j1->equs.end()-1;ii>=j1->equs.begin();--ii){
          Equ* i=*ii;
          VEC_DEL((*i),(&*j1));
          VEC_INS((*i),(&*j));
          VEC_INS(j->equs,i);
          j1->equs.erase(ii);
        }}
        L1:;
      }
      p_vars.push_back(&*j);
      break;
    default:
      delete[] j->name;
      L2:j->name=NULL;
      free(j->foes.data);
      j->foes.data=NULL;
      for(j1=vars.begin();j1<vars.end();++j1)if(j1->f==2)j1->foes.erase(no);
      for(vector<Equ*>::iterator ii=j->equs.begin();ii<j->equs.end();++ii){
        Equ* i=*ii;
        VEC_DEL((*i),(&*j));
      }
  }
  n=p_vars.size();
  vector<Equ>::iterator i1;
  vector<Var*>::iterator jj;
  for(i1=equs.begin()+1;i1<equs.end();++i1)if(i1->n)
  for(vector<Equ>::iterator i2=equs.begin();i2<i1;++i2)if(i2->n&&(*i1)==(*i2)){
    for(jj=i1->begin();jj<i1->end();++jj)VEC_DEL((*jj)->equs,(&*i2));
    i2->n=0;
  }
  j1=vars.begin();
  for(jj=p_vars.end()-1;jj>=p_vars.begin();--jj,++j1){
    Var* j=*jj;
    if(&*j1<j)*j1=*j;
  }
  for(j=j1;j<vars.end();++j){
    j->name=NULL;
    j->foes.data=NULL;
  }
  vars.erase(j1,vars.end());
  vector<Equ*> p_equs;
  i1=equs.begin();
  for(vector<Equ>::iterator i=equs.begin();i<equs.end();++i)if(i->n){
    if(i1<i)*i1=*i;
    for(jj=i1->begin();jj<i1->end();++jj)
      *jj=&*(vars.begin()+((p_vars.end()-lower_bound(p_vars.begin(),p_vars.end(),*jj,greater<Var*>()))-1));
    p_equs.push_back(&*i);
    ++i1;
  }
  equs.erase(i1,equs.end());
  for(j=vars.begin();j<vars.end();++j)
  for(vector<Equ*>:: iterator ii=j->equs.begin();ii<j->equs.end();++ii)
    *ii=&*(equs.begin()+(lower_bound(p_equs.begin(),p_equs.end(),*ii)-p_equs.begin()));
  printf("%d variables, %d equations remain\n",n,equs.size());
}

void Sat01::preprocess(){
  puts("Preprocessing ...");
  vector<Equ>::iterator i;
  list<Var*> q;
  for(i=equs.begin();i<equs.end();++i){
    switch(i->n){
      case 0:throw(false);
      case 1:
        {Var* j=*i->begin();   /* (*i)[0]; */
        if(!j->f)throw(false);
        j->f=1;}
        break;
      default:i->mod=true;
    }
  }
  vector<Var>::iterator j;
  for(j=vars.begin();j<vars.end();++j)if(j->f!=2)q.push_back(&*j);
  list<Equ*> modified;
  reduce(q,modified);
  for(i=equs.begin();i<equs.end();++i){
    i->mod=false;
    if(i->n){
      find_covering_vars(vars,*i,q);
      for(list<Var*>::iterator jj=q.begin();jj!=q.end();++jj)(*jj)->f=0;
      reduce(q,modified);
    }
  }
  while(!modified.empty()){
    Equ* i=modified.front();
    modified.pop_front();
    i->mod=false;
    if(i->n){
      find_covering_vars(vars,*i,q);
      for(list<Var*>::iterator jj=q.begin();jj!=q.end();++jj)(*jj)->f=0;
      reduce(q,modified);
    }
  }
  vector<Equ*>::iterator ii;
  VEMap ve;
  for(j=vars.begin();j<vars.end();++j)if(j->f==2){
    VEMap::iterator p=ve.insert(ve.end(),VEMap::value_type(&*j,vector<Equ*>()));
    vector<Equ*>& c_equs=p->second;
    for(ii=j->equs.begin();ii<j->equs.end();++ii)(*ii)->mod=true;
    u_long* jj=j->foes.data;
    u_long v;
    for(vector<Var>::iterator j1=vars.begin();j1<vars.end();j1+=b_size,++jj){
      v=*jj;
      vector<Var>::iterator j2=j1;
      while(v){
        if((v&1)&&j2->f==2){
          for(ii=j2->equs.begin();ii<j2->equs.end();++ii){
            Equ* i=*ii;
            if(!i->mod){
              VEC_INS(c_equs,i);
              i->mod=true;
            }
          }
        }
        v>>=1;
        ++j2;
      }
    }
    for(ii=j->equs.begin();ii<j->equs.end();++ii)(*ii)->mod=false;
    for(ii=c_equs.begin();ii!=c_equs.end();++ii)(*ii)->mod=false;
  }
  propagate(ve);
  pack();
}

void Sat01::load_bin(const char* f_name){
  FILE* file=fopen(f_name,"rb");
  char sign[8];
  fread(sign,1,7,file);
  sign[7]='\0';
  if(strcmp(sign,"!S01_4!"))throw(false);
  n=read_int(file);
  vars.resize(n,n);
  vector<Var>::iterator j;
  vector<Var*>::iterator jj;
  for(j=vars.begin();j<vars.end();++j){
    int length=read_int(file);
    j->name=new char[length+1];
    fread(j->name,1,length,file);
    *(j->name+length)=0;
    j->f=fgetc(file);
  }
  for(j=vars.begin();j<vars.end();++j)
    fread(j->foes.data,sizeof(u_long),j->foes.data_size,file);
  vector<Equ>::iterator i;
  int m=read_int(file);
  equs.resize(m);
  for(i=equs.begin();i<equs.end();++i){
    int n1=read_int(file);
    *i=Equ(n1);
    for(jj=i->begin();jj<i->end();++jj){
      int no=read_int(file);
      j=vars.begin()+no;
      *jj=&*j;
      j->equs.push_back(&*i);
    }
  }
  m=read_int(file);
  ones.resize(m);
  for(vector<char*>::iterator pp=ones.begin();pp<ones.end();++pp){
    int length=read_int(file);
    *pp=new char[length+1];
    fread(*pp,1,length,file);
    *(*pp+length)=0;
  }
  fclose(file);
  printf("%d variables, %d equations\n",n,equs.size());
}

void Sat01::save_bin(const char* f_name){
  FILE* file=fopen(f_name,"wb");
  fputs("!S01_4!",file);
  vector<Var>::iterator j;
  write_int(vars.size(),file);
  for(j=vars.begin();j<vars.end();++j){
    int length=strlen(j->name);
    write_int(length,file);
    fwrite(j->name,1,length,file);
    fputc(j->f,file);
  }
  for(j=vars.begin();j<vars.end();++j)
    fwrite(j->foes.data,sizeof(u_long),j->foes.data_size,file);
  write_int(equs.size(),file);
  for(vector<Equ>::iterator i=equs.begin();i<equs.end();++i){
    write_int(i->size(),file);
    for(vector<Var*>::iterator jj=i->begin();jj<i->end();++jj)
      write_int(*jj - &*(vars.begin()) ,file);
  }
  write_int(ones.size(),file);
  for(vector<char*>::iterator pp=ones.begin();pp<ones.end();++pp){
    char* p=*pp;
    int length=strlen(p);
    write_int(length,file);
    fwrite(p,1,length,file);
  }
  fclose(file);
}

void Sat01::var_in_equ(int var_no,Equ* equ){
  vector<Var>::iterator var=vars.begin()+var_no;
  for(vector<Var*>::iterator jj=equ->begin();jj<equ->end();++jj){
    Var* j=*jj;
    int j_no = j - &*(vars.begin());
    var->foes.put(j_no);
    j->foes.put(var_no);
  }
  VEC_INS((*equ),&*var);
  VEC_INS(var->equs,equ);
  ++equ->n;
}

void Sat01::load_txt(const char* f_name){
  FILE* file=fopen(f_name,"r");

  char c;
  char buf[16];
  int m,nc;
  fscanf(file,"%c %5s %d %d %d\n",&c,buf,&n,&m,&nc);
  if(c!='p'||strcmp(buf,"SAT01"))throw(false);

  int i;
  vars.resize(n,n);
  for(i=0;i<n;++i){
    sprintf(buf,"x%d",i+1);
    char* name=new char[strlen(buf)+1];
    strcpy(name,buf);
    vars[i].name=name;
  }

  int no,no1;
  equs.resize(m);
  vector<Equ>::iterator e=equs.begin();
  for(i=0;i<m+nc;++i){
    fscanf(file,"%c",&c);
    switch(c){
      case 'e':
        L1:fscanf(file,"%d",&no);
        if(!no){
          fscanf(file,"\n");
          ++e;
          break;
        }
        --no;
        var_in_equ(no,&*e);
        goto L1;
      case 'c':
        fscanf(file,"%d %d\n",&no,&no1);
        --no;
        --no1;
        vars[no].foes.put(no1);
        vars[no1].foes.put(no);
        break;
      default:
        throw(false);
    }
  }

  fclose(file);
  printf("%d variables, %d equations\n",n,equs.size());
}

void Sat01::save_txt(const char* f_name){
  FILE* file=fopen(f_name,"w");

  int nc=0;
  vector<Var>::iterator j, j1, j2;
  u_long* jj1;
  u_long mask;
  for(j=vars.begin()+1;j<vars.end();++j){
    for(j1=vars.begin(),jj1=j->foes.data;j1<j;j1+=b_size,++jj1){
      mask=*jj1;
      j2=j1;
      while(mask&&j2<j){
        if(mask&1)++nc;
        mask>>=1;
        ++j2;
      }
    }
  }

  fprintf(file,"p SAT01 %d %d %d\n",n,equs.size(),nc);

  vector<Var*>::iterator jj;
  for(vector<Equ>::iterator e=equs.begin();e<equs.end();++e){
    fputs("e ",file);
    for(jj=e->begin();jj<e->end();++jj)fprintf(file, "%d ", (*jj - &*(vars.begin())) + 1);
    fputs("0\n",file);
  }

  for(j=vars.begin()+1;j<vars.end();++j){
    for(j1=vars.begin(),jj1=j->foes.data;j1<j;j1+=b_size,++jj1){
      mask=*jj1;
      j2=j1;
      while(mask&&j2<j){
        if(mask&1)fprintf(file,"c %d %d\n",(j-vars.begin())+1,(j2-vars.begin())+1);
        mask>>=1;
        ++j2;
      }
    }
  }

  fclose(file);
}

void Sat01::print_solution(FILE* file){
  fputs("True variables of the found solution:\n",file);
  for(vector<char*>::iterator p=ones.begin();p<ones.end();++p){
    fputs(*p,file);
    fputc('\n',file);
  }
  for(vector<Var>::iterator j=vars.begin();j<vars.end();++j)if(j->f==1){
    fputs(j->name,file);
    fputc('\n',file);
  }
}

int var_weight(Var* var, vector<Var>& vars) {
  /* int result = var->equs.size();
  bit_iterator bi(var->foes);
  int i;
  while((i=bi.next())>-1) result -= vars[i].equs.size(); */
  int result=0;
  vector<Var>::iterator j, j1;
  u_long* jj;
  u_long v;
  for(j=vars.begin(),jj=var->foes.data;j<vars.end();j+=b_size,++jj) {
    v=*jj;
    j1=j;
    while(v) {
      if(v&1) {
        result -= j1->equs.size();
      }
      v>>=1;
      ++j1;
    }
  }
  return result;
}

bool solve(Sat01*& sat01, int& depth, int& max_depth, int& n_guess) {
  depth = max_depth = n_guess = 0;
  char fname[64]="$$$";
  vector<Var>::iterator ext,j;
  L1: try {
    list<Var*> q;
    list<Equ*> modified;
    VEMap ve;
    L2: ext = sat01->vars.begin();
    for(j=ext+1;j<sat01->vars.end();++j) if(
      j->equs.size()==ext->equs.size() ?
      var_weight(&*j,sat01->vars)>var_weight(&*ext,sat01->vars) :
      j->equs.size()>ext->equs.size()
    ) ext=j;
    printf("Guess:\n%s\n",ext->name);
    ++n_guess;
    ext->f=0;
    sprintf(fname+3,"%d.sat01",depth);
    sat01->save_bin(fname);
    if(++depth>max_depth) max_depth = depth;
    printf("Depth=%d\n",depth);
    ext->f=1;
    q.push_back(&*ext);
    sat01->reduce(q,modified);
    sat01->import_modif(modified,ve);
    sat01->propagate(ve);
    sat01->pack();
    goto L2;
  }
  catch(bool result) {
    if(!result) puts("Backtracking ...");
    L3:if(!result&&depth) {
      delete sat01;
      sprintf(fname+3,"%d.sat01",--depth);
      sat01 = new Sat01;
      sat01->load_bin(fname);
      remove(fname);
      printf("Depth=%d\n",depth);
      ext = sat01->vars.begin();
      while(ext->f) ++ext;
      list<Var*> q;
      q.push_back(&*ext);
      try{
        list<Equ*> modified;
        VEMap ve;
        sat01->reduce(q,modified);
        sat01->import_modif(modified,ve);
        sat01->propagate(ve);
        sat01->pack();
      }
      catch(bool result1) {
        result = result1;
        goto L3;
      }
      goto L1;
    }
    for(int no=depth-1;no>=0;--no){
      sprintf(fname+3,"%d.sat01",no);
      remove(fname);
    }
    return result;
  }
}
