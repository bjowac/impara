/*******************************************************************\

Module: Computing shared accesses for a step.

Author: Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/


#ifndef CPROVER_IMPARA_SENSITIVITY_H
#define CPROVER_IMPARA_SENSITIVITY_H

#include <string>
#include <path-symex/locs.h>

#include "../../symex/state.h"

bool abstract_commutation(
    const locst &locs,
    impara_var_mapt &var_map,
    node_reft current,
    node_reft ancestor,
    node_reft mover
);

class abstract_independencet
{
public:

  abstract_independencet(node_reft _current,						                 node_reft _ancestor,
			 node_reft _mover)
  : current(_current),
    ancestor(_ancestor),
    mover(_mover)
  {
  }

	bool operator()(const locst &locs, impara_var_mapt &var_map)
 	{
 		return abstract_commutation(locs, var_map, current, ancestor, mover); 
 	}
 	
  node_reft current;
  node_reft ancestor;
  node_reft mover;
  
  std::string pretty() const;
  
};

typedef std::vector<abstract_independencet> abstract_independence_containert;


#endif




