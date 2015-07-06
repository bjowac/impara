/*******************************************************************\

Module: Solver

Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_IMPARA_SOLVER_H
#define CPROVER_IMPARA_SOLVER_H

#include <util/expr.h>
#include <util/i2string.h>

//#define SMT2

#include <solvers/smt2/smt2_dec.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>


class impara_solver_smt2t :
  public smt2_dect
{
  impara_solver_smt2t(const namespacet &ns) 
  : smt2_dect(ns,
              "impara",
              "impara",
              "AUFBV",
              smt2_convt::Z3),
    activation_literal_counter(0) {}

  typedef literalt contextt;

  contextt new_context();
  void set_context(bool val);
  void set_to_context(contextt context, const exprt &expr, bool val);
  void set_polarity(literalt lit, bool val);
protected:  
  bvt activation_literals;
  unsigned activation_literal_counter;
};

template<typename T>
class impara_solver_baset :
  public bv_pointerst
{
public:
  explicit impara_solver_baset(const namespacet &ns) 
  : bv_pointerst(ns, satcheck),
    activation_literal_counter(0) {}
  
  typedef literalt contextt;

  virtual contextt new_context()
  {
    literalt activation_literal = convert(
      symbol_exprt("context::\\act$"+
      i2string(activation_literal_counter++), bool_typet()));

    set_frozen(activation_literal);
    activation_literals.push_back(activation_literal);
    set_assumptions(activation_literals);
    return !activation_literal;
  }
  
  virtual void set_context(bool val)
  {
    assert(!activation_literals.empty());
    literalt activation_literal = activation_literals.back();
    activation_literals.pop_back();
    set_to(literal_exprt(activation_literal), val);
    set_assumptions(activation_literals);
  }
  
  virtual void set_to_context(contextt context, const exprt &expr, bool val)
  {
    const exprt &tmp=val ? expr : not_exprt(expr);

    literalt lit=(*this)(tmp);
    (*this) << or_exprt(literal_exprt(lit), literal_exprt(context));
  }
  
  virtual void set_polarity(literalt lit, bool val)
  {
    //satcheck.set_polarity(lit, val);
  }
 
  T satcheck;

  
  virtual bool is_eliminated(literalt literal) 
  {
    return false;
  }
  
protected:  
  bvt activation_literals;
  unsigned activation_literal_counter;
};


class impara_solver_simplifiert : 
  public impara_solver_baset<satcheck_minisat_simplifiert>
{
public:
  impara_solver_simplifiert(const namespacet &ns) 
  : impara_solver_baset(ns) {}


  virtual bool is_eliminated(literalt literal)
  {
    return satcheck.is_eliminated(literal);
  }
};

class impara_solver_no_simplifiert : 
  public impara_solver_baset<satcheck_minisat_no_simplifiert>
{
public:
  impara_solver_no_simplifiert(const namespacet &ns) 
  : impara_solver_baset(ns) {}

};

typedef impara_solver_simplifiert impara_solvert;

#endif
