/*******************************************************************\

Module: Interval-based VCC checker

Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_IMPARA_INTERVAL_CHECKER_H
#define CPROVER_IMPARA_INTERVAL_CHECKER_H


#include "symex/state.h"
#include "symex/impara_history.h"

#include "domains/interval_dom.h"

#include "interpolate/interpolator.h"

class interval_checkert 
  : public interpolatort
{
 public:
 
  interval_checkert(
    const namespacet& _ns,
    const optionst& _options)
    : interpolatort(_ns, _options)
  {
  }
 
  virtual decision_proceduret::resultt operator()(
    impara_step_reft history,
    node_reft node_ref,
    node_reft ancestor,
    const exprt& start,
    const exprt& cond,
    interpolant_mapt&);
   
   
   interval_domt interval_dom; 

 protected:
   typedef hash_set_cont<irep_idt, irep_id_hash> symbol_sett;
 
   symbol_sett depends;
   impara_step_reft history;
   node_reft ancestor;
	
   void relevant_assignments();
};

  
#endif
