/*******************************************************************\

Module: Eliminate quantifiers

Author: Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_QUANTIFIER_ELIMINATION_H
#define CPROVER_QUANTIFIER_ELIMINATION_H


exprt eliminate_forall(
  const symbol_exprt &quantifier,
  const exprt &src,
  const namespacet &ns);

bool has_symbol(
  const symbol_exprt &s,
  const exprt &where);

  
#endif
