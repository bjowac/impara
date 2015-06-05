/*******************************************************************\

Module: Interpolation

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_INTERPOLATOR_H
#define CPROVER_IMPARA_INTERPOLATOR_H

#include <util/options.h>
#include <path-symex/locs.h>

#include <nodes.h>


bool smt2horn(
    impara_step_reft history,
    std::string &result);

#endif
