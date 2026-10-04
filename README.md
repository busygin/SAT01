# SAT01

SAT01 asks for x in {0,1}^n such that every equation sum_{j in e} x_j = 1 holds
and x_i x_j = 0 for every contradiction (i,j), any two variables of an equation
contradicting each other.  `sat01theta.tex` describes the framework and how NP
problems reduce to it.

## Building

The bit vectors come from the library of
[QUALEX-MS](https://github.com/busygin/qualex-ms), a git submodule here:

    git clone --recursive https://github.com/busygin/SAT01.git
    cd SAT01
    make

(`git submodule update --init` fetches it in a clone made without
`--recursive`, and `make QMS=<directory>` builds against another checkout of
qualex-ms.)  The code is C++20 and needs nothing beyond the C++ library.

## Programs

    sat01 [+/-t] [-d<dir>] [-l<log_file>] <sat01_file>

solves an instance, binary (default) or text (`+t`), writing the solution to
`<name>.out`.  Propagation runs unit propagation, the covering (clique)
analysis and the contradiction analysis; the search guesses a variable true and
backtracks to its negation.  `-d<dir>` saves the instance at every guess to
`<dir>/guess<k>_depth<d>.sat01` for analysis, and `-l<log_file>` logs every
deduction of propagation.

    factor2sat01 <number>          the factoring of a number as <number>.sat01
    hcp2sat01 <hcp_file>           a Hamiltonian cycle problem (TSPLIB format)
    factor_out2sol <out_file>      the factors from a solution of factor2sat01's instance
    sat012clique [-w] [-p] <file>  the instance as a clique problem (see its usage)
    sat01qms [-s] [-m] <file>      QUALEX-MS on the propagated instance, without search

`sat01qms` runs the full propagation and then QUALEX-MS on the clique problem
left, on the equation wrapper or (`-s`) the standard clique wrapper, with its
stationary points at the radius of a clique of weight m with `-m`; it is built
with `make sat01qms` and needs a LAPACK and a CBLAS (OpenBLAS by default).

`factor.sh <number>` factors a number with these.

## Source files

- `sat01.h`: the instance, variables and equations referring to each other by
  index, so that a state of the solver is a value that can be copied
- `sat01_io.cpp`: the binary and text formats
- `propagation.cpp`: the three analyses and preprocessing
- `pack.cpp`: removal of the assigned variables, merging of twins and of
  duplicate equations
- `search.cpp`: the guesses and backtracking, which keeps the states in memory
- `main.cpp`: the solver's command line
