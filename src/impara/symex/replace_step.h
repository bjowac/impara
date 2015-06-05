/*******************************************************************\

Module: History for path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com
        
\*******************************************************************/

#ifndef CPROVER_REPLACE_STEP_H
#define CPROVER_REPLACE_STEP_H

#include <vector>
#include <util/replace_expr.h>

class impara_stept;

bool replace_step(const replace_mapt &what, impara_stept &dest);
bool replace_steps(const replace_mapt &what, std::vector<impara_stept> &dest);

#endif

