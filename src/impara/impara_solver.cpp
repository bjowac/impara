/*******************************************************************\

Module: Solver

Author: Bjoern Wachter, bjoern.wachter@gmail.com


\*******************************************************************/

#include <util/i2string.h>
#include <cstdlib>
#include <algorithm>


#include <util/time_stopping.h>

#include "impara_solver.h"

#define DEBUG

#ifdef DEBUG
#include <langapi/language_util.h>
#include <iostream>
#endif


void impara_solver_smt2t::set_polarity(literalt lit, bool val)
{
#ifndef SMT2
//  satcheck.set_polarity(lit, val);
#endif
}

/*******************************************************************\

Function: impara_solver_smt2t::set_to_context

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/ 
 
 
void impara_solver_smt2t::set_to_context(contextt context, const exprt &expr, bool val)
{
  const exprt &tmp=val ? expr : not_exprt(expr);

  literalt lit=(*this)(tmp);
  (*this) << or_exprt(literal_exprt(lit), literal_exprt(context));
}
 
/*******************************************************************\

Function: impara_solver_smt2t::new_context

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/ 

literalt impara_solver_smt2t::new_context()
{
  literalt activation_literal = convert(
      symbol_exprt("context::\\act$"+
      i2string(activation_literal_counter++), bool_typet()));

  set_frozen(activation_literal);
  activation_literals.push_back(activation_literal);
  set_assumptions(activation_literals);
  return !activation_literal;
}
  
  



