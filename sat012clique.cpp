#include <string.h>
#include <exception>
#include <string>

#include "sat01.h"

// sat012clique() writes the unweighted clique graph: each variable becomes a
// clique of as many vertices as it has equations, two vertices of different
// variables are adjacent iff the variables do not contradict, and the
// instance is satisfiable iff the graph has a clique of size m (the number of
// equations)
void sat012clique(const Sat01& sat01, const char* fname) {
  size_t n_vert = 0;
  size_t n_vars = sat01.vars.size();

  std::vector<size_t> var_inds(n_vars+1);
  for (size_t i=0; i<n_vars; ++i) {
    var_inds[i] = n_vert;
    n_vert += sat01.vars[i].equations.size();
  }
  var_inds.back() = n_vert;

  std::vector<bool> adj_mat(n_vert*n_vert, true);
  for (size_t i=0; i<n_vert; ++i) adj_mat[i*(n_vert+1)] = false;

  printf("n_vert=%ld\n", n_vert);

  for (size_t i=0; i<n_vars; ++i)
    for (int j : sat01.vars[i].foes.ones())
      for (size_t k1=var_inds[i]; k1<var_inds[i+1]; ++k1)
        for (size_t k2=var_inds[j]; k2<var_inds[j+1]; ++k2)
          adj_mat[k1*n_vert+k2] = false;

  size_t n_edges = 0;
  for(size_t i=1; i<n_vert; ++i)
    for(size_t j=0; j<i; ++j) {
      // sanity check: adj_mat is symmetric
      if (adj_mat[i*n_vert+j] != adj_mat[j*n_vert+i]) {
        printf("Error: A(%ld,%ld)=%ld while A(%ld,%ld)=%ld\n", i, j, size_t(adj_mat[i*n_vert+j]), j, i, size_t(adj_mat[j*n_vert+i]));
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

// sat012wclique() keeps one vertex per SAT01 variable and passes the weights
// through: vertex j gets the weight w_j = number of equations containing
// x_j, two vertices are adjacent iff their variables do not contradict, and
// the instance is satisfiable iff the graph has a clique of weight m (the
// number of equations).  It writes <base>.clq.b, a binary DIMACS graph whose
// preamble carries the weights as "n v w" lines after the "p" line (cliquer
// reads them there, QUALEX-MS stops at the "p" line), <base>.w, the weights
// one per line for the -w option of QUALEX-MS, and <base>.equ, one equation
// per line as the 1-based vertices of its variables.  It writes no <base>.clq,
// so the output of the unweighted conversion is left alone.
void sat012wclique(const Sat01& sat01, const char* base) {
  size_t n = sat01.vars.size();
  size_t m = sat01.equs.size();

  std::vector<bool> adj_mat(n*n, true);
  for (size_t i=0; i<n; ++i) adj_mat[i*(n+1)] = false;
  for (size_t i=0; i<n; ++i)
    for (int j : sat01.vars[i].foes.ones())
      adj_mat[i*n+j] = adj_mat[j*n+i] = false;
  size_t n_edges = 0;
  for (size_t i=1; i<n; ++i)
    for (size_t j=0; j<i; ++j)
      if (adj_mat[i*n+j]) ++n_edges;

  std::vector<size_t> w(n);
  size_t zero = 0;
  for (size_t i=0; i<n; ++i) {
    w[i] = sat01.vars[i].equations.size();
    if (!w[i]) ++zero;
  }
  if (zero) printf("Warning: %zu variables are in no equation (weight 0)\n", zero);
  printf("%zu vertices, %zu edges, required clique weight %zu\n", n, n_edges, m);

  std::string b(base);
  char line[64];
  snprintf(line, sizeof(line), "p edge %zu %zu\n", n, n_edges);
  std::string preamble = "c SAT01 instance, required clique weight "
    + std::to_string(m) + "\n" + line;
  for (size_t i=0; i<n; ++i) {
    snprintf(line, sizeof(line), "n %zu %zu\n", i+1, w[i]);
    preamble += line;
  }

  // binary DIMACS: the preamble length, the preamble, then for each vertex i
  // the bits of its adjacency to j = 0..i, most significant bit first, in
  // (i>>3)+1 bytes
  FILE* f = fopen((b+".clq.b").c_str(), "wb");
  fprintf(f, "%zu\n", preamble.size());
  fwrite(preamble.data(), 1, preamble.size(), f);
  std::vector<unsigned char> row;
  for (size_t i=0; i<n; ++i) {
    row.assign((i>>3)+1, 0);
    for (size_t j=0; j<i; ++j)
      if (adj_mat[i*n+j]) row[j>>3] |= (unsigned char)(0x80>>(j&7));
    fwrite(row.data(), 1, row.size(), f);
  }
  fclose(f);

  f = fopen((b+".w").c_str(), "w");
  for (size_t i=0; i<n; ++i) fprintf(f, "%zu\n", w[i]);
  fclose(f);

  f = fopen((b+".equ").c_str(), "w");
  for (size_t e=0; e<m; ++e) {
    const Equation& equ = sat01.equs[e];
    for (size_t k=0; k<equ.vars.size(); ++k)
      fprintf(f, k ? " %d" : "%d", equ.vars[k]+1);
    fputc('\n', f);
  }
  fclose(f);
}

int main(int argc, char** argv) {
  bool weighted = false, full = false;
  int a = 1;
  for (; a < argc-1; ++a) {
    if (!strcmp(argv[a], "-w")) weighted = true;
    else if (!strcmp(argv[a], "-p")) full = true;
    else break;
  }
  if (a != argc-1) {
    puts("Syntax: sat012clique [-w] [-p] <sat01_file>\n"
         "Writes <base>.clq, an unweighted graph in which each variable is a\n"
         "clique of as many vertices as it has equations; with -w, one vertex\n"
         "per variable weighted by its number of equations: <base>.clq.b,\n"
         "<base>.w and <base>.equ.  The instance is first reduced by eliminating\n"
         "the assigned variables, or with -p by the full preprocessing of the\n"
         "solver, whose contradiction analysis also adds derived contradictions.");
    return 1;
  }
  const char* name = argv[a];

  Sat01 sat01;
  try {
    sat01.load_bin(name);
  }
  catch (const std::exception& error) {
    printf("ERROR: %s\n", error.what());
    return 1;
  }

  Status status = full ? sat01.preprocess() : sat01.light_preprocess();
  if (status != Status::open) {
    bool solved = status == Status::solved;
    if(weighted){
      puts(solved ? "A solution has been found by preprocessing."
                  : "Preprocessing has revealed that no solution exists.");
    }else if(solved){
      puts("Factoring has been found by preprocessing.");
    }else{
      puts("Preprocessing has revealed that no factoring exists.");
    }
    return 1;
  }

  std::string base(name);
  size_t dot = base.rfind(".sat01");
  if (dot != std::string::npos) base.erase(dot);
  if (weighted) sat012wclique(sat01, base.c_str());
  else sat012clique(sat01, (base+".clq").c_str());

  return 0;
}
