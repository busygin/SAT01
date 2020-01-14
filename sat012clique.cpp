#include "sat01.h"

void sat012clique(const Sat01& sat01, const char* fname) {
  size_t n_vert = 0;
  size_t n_vars = sat01.vars.size();

  std::vector<size_t> var_inds(n_vars+1);
  for (size_t i=0; i<n_vars; ++i) {
    var_inds[i] = n_vert;
    n_vert += sat01.vars[i].equs.size();
  }
  var_inds.back() = n_vert;

  std::vector<bool> adj_mat(n_vert*n_vert, true);
  for (size_t i=0; i<n_vert; ++i) adj_mat[i*(n_vert+1)] = false;

  printf("n_vert=%ld\n", n_vert);

  for (size_t i=0; i<n_vars; ++i) {
    const bool_vector& foes = sat01.vars[i].foes;
    u_long* jj;
    size_t j;
    for (j=0, jj=foes.data; j<n_vars; j+=b_size,++jj) {
      u_long v = *jj;
      size_t j1=j;
      while(v) {
        if (v&1) {
          for (size_t k1=var_inds[i]; k1<var_inds[i+1]; ++k1)
            for (size_t k2=var_inds[j1]; k2<var_inds[j1+1]; ++k2)
              adj_mat[k1*n_vert+k2] = false;
        }
        v>>=1;
        ++j1;
      }
    }
  }


  size_t n_edges = 0;
  for(size_t i=1; i<n_vert; ++i)
    for(size_t j=0; j<i; ++j) {
      // sanity check: adj_mat is symmetric
      if (adj_mat[i*n_vert+j] != adj_mat[j*n_vert+i]) {
        printf("Error: A(%ld,%d)=%ld while A(%ld,%d)=%ld\n", i, j, size_t(adj_mat[i*n_vert+j]), j, i, size_t(adj_mat[j*n_vert+i]));
        throw false;
      }


      if (adj_mat[i*n_vert+j]) ++n_edges;
    }


  printf("Required clique size: %ld\n", sat01.equs.size());

  FILE* f = fopen(fname, "w");
  fprintf(f, "c Required clique size: %ld\n", sat01.equs.size());
  fprintf(f, "p edge %ld %ld\n", n_vert, n_edges);
  for(size_t i=0; i<n_vert-1; ++i)
    for(size_t j=i+1; j<n_vert; ++j)
      if (adj_mat[i*n_vert+j])
        fprintf(f, "e %ld %ld\n", i+1, j+1);

  fclose(f);
}

int main(int argc, char** argv) {
  if (argc==2) {
    const char* name = argv[1];

    Sat01* sat01 = new Sat01;
    sat01->load_bin(name);

    int i=strlen(name);
    char* clq_file_name=new char[i+7];
    memcpy(clq_file_name,name,i+1);
    char* p=strstr(clq_file_name,".sat01");
    if(!p) p=clq_file_name+i;
    strcpy(p,".clq");

    try{sat01->light_preprocess();}
    catch(bool result){
      if(result){
        puts("Factroing has been found by preprocessing.");
      }else{
        puts("Preprocessing has revealed that no factoring exists.");
      }
      return 1;
    }

    sat012clique(*sat01, clq_file_name);

    delete[] clq_file_name;
    delete sat01;
  }

  return 0;
}
