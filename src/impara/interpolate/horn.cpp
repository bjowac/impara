/*******************************************************************\

Module: Interpolator based on weakest precondition

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>

#include "symex/from_ssa.h"

#include "step_wp.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

class horn_problemt
{
public:

  void add(impara_step_reft &history);


  typedef symbol_exprt terminalt;
  std::vector<terminalt> terminals;

  typedef exprt clauset;
  std::vector<clauset> clauses;

  std::string pretty();

  // SMT 2 output
  void output(std::ostream &o);
};

void horn_problemt::add(impara_step_reft &history)
{
  // identify terminals -- everything that is covered or covers s.t.



  //




}


bool smt2horn(
    impara_step_reft history,
    std::string &result)
{


  return false;

}




