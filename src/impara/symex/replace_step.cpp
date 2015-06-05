/*******************************************************************\

Module: History of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>
#include <path-symex/locs.h>




#include "state.h"
#include "../nodes.h" // NOTE: remove for CPROVER main branch

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include "replace_step.h"

#include "impara_history.h"

bool replace_step(const replace_mapt &what, impara_stept &dest)
{
	// create new expressions
  bool result1=replace_expr(what, dest.guard);
  bool result2=replace_expr(what, dest.full_lhs);
  bool result3=replace_expr(what, dest.ssa_lhs);
  bool result4=replace_expr(what, dest.ssa_rhs);

 	// report result 
  return result1 || result2 || result3 || result4;
}

bool replace_steps(const replace_mapt &what, std::vector<impara_stept> &dest)
{
	bool result=false;

	for(unsigned i=0; i<dest.size(); ++i)
		result = replace_step(what, dest[i]) || result;

	return result;
}

