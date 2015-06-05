/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_INTERVAL_DOMAIN_H
#define CPROVER_INTERVAL_DOMAIN_H

#include <util/ieee_float.h>
#include <util/mp_arith.h>

#include "intervals.h"

class interval_domt
{
public:
  // trivial, conjunctive interval domain for both float
  // and integers
  
  typedef std::map<irep_idt, integer_intervalt> int_mapt;
  typedef std::map<irep_idt, ieee_float_intervalt> float_mapt;

  int_mapt int_map;
  float_mapt float_map;
              
  virtual void output(
    const namespacet &ns,
    std::ostream &out) const;

  bool merge(const interval_domt &b);
  
  exprt make_expression(const symbol_exprt &) const;
  
  static bool is_int(const typet &src)
  {
    return src.id()==ID_signedbv || src.id()==ID_unsignedbv;
  }
  
  static bool is_float(const typet &src)
  {
    return src.id()==ID_floatbv;
  }

  int eval(const exprt &);
  
  void havoc_rec(const exprt &);
  void assume_rec(const exprt &, bool negation=false);
  void assume_rec(const exprt &lhs, irep_idt id, const exprt &rhs);
  void assign(const exprt& lhs, const exprt& rhs);

protected:
  integer_intervalt eval_int_rec(const exprt &);
  ieee_float_intervalt eval_float_rec(const exprt &);

  integer_intervalt get_int_rec(const exprt &);
  ieee_float_intervalt get_float_rec(const exprt &);
};

#endif
