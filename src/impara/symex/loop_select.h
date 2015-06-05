/*******************************************************************\

Module: History for path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com
        
\*******************************************************************/

#ifndef CPROVER_IMPARA_LOOP_SELECT_H
#define CPROVER_IMPARA_LOOP_SELECT_H

#include "impara_history.h"

/*
 The following input:

 steps:
 0: x0 = 1
 1  y0 = 0
 2: x1 = 2
 3: x1 > 0
 4: y1 = x1 + 1
 5: x2 = y1
 ls: ls
 where: 3

 is transformed into

 0: x0 = 1
 1  y0 = 0
 2: x1 = 2
 ------
 xphi1 = ls ? x2 : x1
 yphi0 = ls ? y1 : y0
 3: xphi1 > 0
 ------
 4: xphi1 > 0 => y1 = x1 + 1
 5: xphi1 > 0 => x2 = y0
 
 More concisely:

 x_phi = ls ? x_post : x_pre
 guard => x_post = e [x_pre / x_phi] 
 */

#include <util/replace_expr.h>

void loop_select(std::vector<impara_stept> &steps,  // input / output (in-place modification)
                 symbol_exprt &ls,                      // input
		 unsigned distance,                     // input 
		 replace_mapt &vars)                // input
{
  std::string phi="phi";

  replace_mapt phi_map;

  // produce phi symbol for each pre symbol
  for(replace_mapt::const_iterator
      var_it=vars.begin();
      var_it!=vars.end();
      ++var_it)
  {
    const symbol_exprt &symbol=to_symbol_expr(var_it->first);
   

    // get the base name
    std::string identifier=id2string(symbol.get_identifier());

    // attach a phi
    std::string phi_identifier=identifier+phi;

    // create symbol
    symbol_exprt phi_symbol(phi_identifier, symbol.type());

    phi_map[symbol]=phi_symbol;

    exprt rhs=if_exprt(phi_symbol, symbol, var_it->second);
  }  

  // replace lhs with phi	
  for(int i=distance; i>=0; --i)
  {
    impara_stept &step=steps[i];
    replace_expr(phi_map, step.guard);
    replace_expr(phi_map, step.ssa_rhs);
  }

  // bind phi nodes

  // treat guards
 
}

#endif
