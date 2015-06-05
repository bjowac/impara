/*******************************************************************\

Module: Computing shared accesses for a step.

Author: Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/


#ifndef CPROVER_IMPARA_SHARED_STEP_H
#define CPROVER_IMPARA_SHARED_STEP_H

#include "../../symex/state.h"

class shared_stept
{
public:

  typedef std::set<exprt> sett;

  shared_stept(const locst &_locs,
               impara_var_mapt &_var_map, 
               const impara_stept &_step,
               bool _pointers_only)
		: locs(_locs),
		  var_map(_var_map), 
		  step(_step),
		  pointers_only(_pointers_only)
  {}

  void operator()(sett& reads, sett& writes);

  void operator()(exprt& expr, sett& reads)
  {
    shared_rec(expr, reads);
  }

  static bool intersect(const sett& a, const sett& b);
 
  static bool conflict(const sett& reads1, const sett& writes1,
                       const sett& reads2, const sett& writes2);

  static void output(const sett &set, std::ostream &out);
  static void output(const sett &reads, const sett &writes, std::ostream &out);

protected:
  const locst &locs;
  impara_var_mapt &var_map;
  const impara_stept &step;
  bool pointers_only;

  void process_step(const impara_stept &step, sett& reads, sett& writes);

  bool shared_rec(const exprt& expr, sett& vars);
};

#endif




