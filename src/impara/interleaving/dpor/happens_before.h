/*******************************************************************\

Module: 

Author: Bjorn Wachter, Subodh Sharma

\*******************************************************************/

#ifndef CPROVER_IMPARA_HAPPENS_BEFORE_H
#define CPROVER_IMPARA_HAPPENS_BEFORE_H

#include <vector>

#include <util/std_expr.h>
#include <symex/var_map.h>
#include <path-symex/locs.h>
#include <symex/impara_history.h>

#include "clocks.h"

#include "nodes.h"

typedef std::set<unsigned> thread_sett;
typedef std::map<node_reft, thread_sett > backtrackt;

void happens_before(locst &__locs,
                  impara_var_mapt &__var_map,
                  std::vector<impara_step_reft>& __steps,
                  node_reft terminal, 
                  backtrackt &__backtrack,
                  bool only_pointers);


#endif
