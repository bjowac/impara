/*******************************************************************\

Module: Compute disjunction and conjunction of expressions.


Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_JOIN_H
#define CPROVER_IMPARA_JOIN_H


bool implies(const exprt& e1, const exprt& e2, const class namespacet& ns);

void impara_constrain(const exprt &source, exprt &target, const class namespacet& ns);

void impara_conjoin(const exprt &source, exprt &target, const class namespacet& ns);
void impara_disjoin(const exprt &source, exprt &target, const class namespacet& ns);
  
#endif
