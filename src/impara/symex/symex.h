/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_H
#define CPROVER_PATH_SYMEX_H

#include <path-symex/locs.h>
#include "state.h"

// Transform a state by executing a single statement.
// May occasionally yield more than one successor state
// (branches, function calls with trinary operator),
// which are put into "further_states".

void impara_symex(
  statet &state,
  std::list<statet> &further_states);

// Transform a state by executing a single statement.
// Will fail if there is more than one successor state.
void impara_symex(statet &state);

// Transforms a state by executing a goto statement;
// the 'taken' argument indicates which way.
void impara_symex_goto(
  statet &state,
  bool taken);

// Transforms a state by executing an assertion statement;
// it is enforced that the assertion fails.
void impara_symex_assert_fail(
  statet &state);

#endif
