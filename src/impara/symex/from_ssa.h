/*******************************************************************\

Module: Map SSA expressions back to expression over program variables

Author: Bjorn Wachter, bjoern.wachter@gmail.com
        
\*******************************************************************/

#ifndef CPROVER_IMPARA_FROM_SSA_H
#define CPROVER_IMPARA_FROM_SSA_H

#include <set>
#include <util/std_expr.h>
#include <util/replace_expr.h>

// from SSA expression back to expression (NOTE: not in path_symex)
exprt from_ssa(const exprt &src);

void from_ssa(const std::set<symbol_exprt> &in,
                       replace_mapt &out);



#endif
