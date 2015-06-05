/*******************************************************************\

Module: Computing a WP of a step

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STEP_WP_H
#define CPROVER_STEP_WP_H

#include "symex/state.h"
#include "symex/impara_history.h"

exprt step_wp(
  const impara_stept &,
  const exprt &,
  bool quantified,
  const namespacet &
);
  
#endif
