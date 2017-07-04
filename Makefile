# Makefile of SAT01 solver for GNU make

CFLAGS = -DNDEBUG -O3 -Wall
LINKFLAGS = -s

CC = gcc
CXX = g++

HEADERS = bool_vector.h bin_store.h
SAT01_src = main.cpp sat01.cpp bool_vector.cpp
FACTOR2SAT01_src = factor2sat01.cpp bool_vector.cpp
FACTOR_OUT2SOL_src = factor_out2sol.cpp
EXECUTABLES = sat01 factor2sat01 factor_out2sol

all: $(HEADERS) $(SAT01_src) $(FACTOR2SAT01_src) $(FACTOR_OUT2SOL_src) $(EXECUTABLES)

sat01: $(HEADERS) $(SAT01_src)
	$(CXX) $(LINKFLAGS) $(CFLAGS) $(SAT01_src) -o $@

factor2sat01: $(HEADERS) $(FACTOR2SAT01_src)
	$(CXX) $(LINKFLAGS) $(CFLAGS) $(FACTOR2SAT01_src) -o $@

factor_out2sol: $(FACTOR_OUT2SOL_src)
	$(CXX) $(LINKFLAGS) $(CFLAGS) $(FACTOR_OUT2SOL_src) -o $@

clean:
	rm $(EXECUTABLES)
