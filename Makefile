# Makefile of SAT01 solver for GNU make
#
#   make [QMS=<directory of qualex-ms>]
#   make sat01qms [BLAS_LIBS=<link line>]
#
# SAT01 takes its bit vectors from the combinatorial core of the QUALEX-MS
# library (lib/ of qualex-ms), which is a git submodule here: fetch it with
# "git submodule update --init", or point QMS to another checkout.  sat01qms,
# which runs QUALEX-MS on a propagated instance, links the whole library on its
# CPU backend and so needs a LAPACK and a CBLAS (BLAS_LIBS, -lopenblas by
# default); it is not part of "make".

QMS ?= qualex-ms
BUILD = build

ifneq ($(MAKECMDGOALS),clean)
ifeq ($(wildcard $(QMS)/lib/bool_vector.h),)
$(error QUALEX-MS not found in $(QMS): run "git submodule update --init" or make QMS=<directory of qualex-ms>)
endif
endif

CXX = g++
CXXFLAGS = -std=gnu++20 -DNDEBUG -Ofast -Wall -I$(QMS)/lib
LINKFLAGS = -s

QMS_CORE = $(BUILD)/qms/libqms_core.a
QMS_LIB = $(BUILD)/qms/libqms.a
BLAS_LIBS ?= -lopenblas
SOLVER = $(addprefix $(BUILD)/,sat01_io.o propagation.o pack.o search.o)
EXECUTABLES = sat01 sat012clique factor2sat01 hcp2sat01 factor_out2sol

all: $(EXECUTABLES)

sat01: $(BUILD)/main.o $(SOLVER) $(QMS_CORE)
	$(CXX) $(LINKFLAGS) -o $@ $^

sat012clique: $(BUILD)/sat012clique.o $(SOLVER) $(QMS_CORE)
	$(CXX) $(LINKFLAGS) -o $@ $^

factor2sat01: $(BUILD)/factor2sat01.o $(QMS_CORE)
	$(CXX) $(LINKFLAGS) -o $@ $^

hcp2sat01: $(BUILD)/hcp2sat01.o $(QMS_CORE)
	$(CXX) $(LINKFLAGS) -o $@ $^

factor_out2sol: $(BUILD)/factor_out2sol.o
	$(CXX) $(LINKFLAGS) -o $@ $^

sat01qms: $(BUILD)/sat01qms.o $(SOLVER) $(QMS_LIB)
	$(CXX) $(LINKFLAGS) -o $@ $^ $(BLAS_LIBS)

$(BUILD)/%.o: %.cpp $(wildcard *.h) $(QMS)/lib/bool_vector.h | $(BUILD)
	$(CXX) $(CXXFLAGS) -c $< -o $@

$(QMS_CORE): $(wildcard $(QMS)/lib/*.cc $(QMS)/lib/*.h)
	$(MAKE) -C $(QMS)/lib core BUILD=$(abspath $(BUILD)/qms)

$(QMS_LIB): $(wildcard $(QMS)/lib/*.cc $(QMS)/lib/*.c $(QMS)/lib/*.h)
	$(MAKE) -C $(QMS)/lib GPU=0 BUILD=$(abspath $(BUILD)/qms)

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD) $(EXECUTABLES) sat01qms

.PHONY: all clean
