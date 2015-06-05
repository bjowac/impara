/*******************************************************************\

Module: Solver

Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_IMPARA_SOLVER_H
#define CPROVER_IMPARA_SOLVER_H

#include <util/expr.h>

//#define SMT2

#ifdef SMT2

#include <solvers/smt2/smt2_dec.h>

#else

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#endif

class impara_solvert : 
#ifdef SMT2
  public smt2_dect
#else
  public bv_pointerst
#endif
{
public:

#ifdef SMT2
  impara_solvert(const namespacet &ns) 
  : smt2_dect(ns,
              "impara",
              "impara",
              "AUFBV",
              smt2_convt::Z3),
    activation_literal_counter(0)
  {
  }

#else
  impara_solvert(const namespacet &ns) 
  : bv_pointerst(ns, satcheck),
    activation_literal_counter(0)
  {
  }
#endif

  typedef literalt contextt;


  contextt new_context();
  void set_context(bool val);
  
  void set_to_context(contextt context, const exprt &expr, bool val);

  void set_polarity(literalt lit, bool val);
#ifdef SMT2

#else
  #ifdef SATCHECK_GLUCOSE
  satcheck_glucose_no_simplifiert satcheck;
  #else
  satcheck_minisat_no_simplifiert satcheck;
  #endif
#endif

protected:  
  bvt activation_literals;
  unsigned activation_literal_counter;
};

  
#endif
