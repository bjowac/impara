include ../../config.inc

SRC = \
      shared.cpp\
      symex.cpp \
      state.cpp \
      build_goto_trace.cpp\
      impara_history.cpp\
      var_map.cpp\
      propagation.cpp

INCLUDES= -I $(CBMC)/src -I .. 

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CP_CXXFLAGS +=-g
LINK_FLAGS=
CLEANFILES = symex$(LIBEXT)

all: symex$(LIBEXT)

###############################################################################

symex$(LIBEXT): $(OBJ) 
	$(LINKLIB)

