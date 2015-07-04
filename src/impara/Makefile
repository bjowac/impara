include ../config.inc

IMPARA_DIRS = symex interpolate interleaving

SRC = main.cpp\
      impara_parse_options.cpp\
      impara_path_search.cpp\
      impara_join.cpp\
      impara_solver.cpp\
      binsearch_utils.cpp\
      dot_output.cpp \
      cover.cpp\
      strengthen.cpp\
      symex/shared.cpp\
      symex/symex.cpp \
      symex/state.cpp \
      symex/state_read.cpp\
      symex/build_goto_trace.cpp\
      symex/impara_history.cpp\
      symex/replace_step.cpp\
      symex/var_map.cpp\
      symex/propagation.cpp\
      symex/impara_symex_replay.cpp\
      symex/from_ssa.cpp\
      interpolate/horn.cpp\
      interpolate/interpolator.cpp\
      interpolate/step_wp.cpp\
      interpolate/quantifier_elimination.cpp\
      interpolate/wordlevel_interpolator.cpp\
      interpolate/wordlevel_axioms.cpp\
      dot_output.cpp\
      nodes.cpp\
      interleaving/mpor/partial_order_reduction.cpp\
      interleaving/utility/shared_step.cpp\
      simple_checker.cpp\
      interval_checker.cpp\
      interleaving/utility/dependency_check.cpp\
      interleaving/mpor/dependency_chain.cpp\
      domains/interval_dom.cpp\
      $(CBMC)/src/cbmc/xml_interface.cpp

OBJ+= $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/cpp/cpp$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/analyses/analyses$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/path-symex/path-symex$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT)

INCLUDES= -I $(CBMC)/src -I .

LIBS =

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CLEANFILES = impara$(EXEEXT)

$(patsubst %, %.dir, $(IMPARA_DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)


CP_CXXFLAGS += 
LINKFLAGS +=

all: impara$(EXEEXT)

ifneq ($(wildcard $(CBMC)/src/java/Makefile),)
  OBJ += $(CBMC)/src/java/java$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JAVA
endif

ifneq ($(wildcard $(CBMC)/src/specc/Makefile),)
  OBJ += $(CBMC)/src/specc/specc$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_SPECC
endif

ifneq ($(wildcard $(CBMC)/src/php/Makefile),)
  OBJ += $(CBMC)/src/php/php$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

impara$(EXEEXT): $(OBJ)
	$(LINKBIN)
