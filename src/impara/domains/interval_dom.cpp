/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>
#include <util/arith_tools.h>


#include <langapi/language_util.h>
#include <iostream>


#include "interval_dom.h"


/*******************************************************************\

Function: interval_domt::eval

  Inputs:

 Outputs: +1 = true, 0 = don't know, -1 = false

 Purpose:

\*******************************************************************/


int interval_domt::eval(const exprt &src)
{
  if(src.id()==ID_and)
  {
    std::cout << "AND" << std::endl;
 
    bool unknown=false;

    const exprt::operandst& operands=src.operands();

    for(unsigned i=0; i<operands.size(); ++i)
    {
      int result=eval(operands[i]);
       
      switch(result)
      {
        case 0: 
          unknown=true;
          break;
        case -1:
          return false;
          break;
        case 1:
          break;
      }

      if(unknown)
        return 0;
      else
        return 1;
    }
  } 
  else if(src.id()==ID_or)
  {
    bool unknown=false;

    for(unsigned i=0; i<src.operands().size(); ++i)
    {
      int result=eval(src.operands()[i]);
       
      switch(result)
      {
        case 0: 
          unknown=true;
          break;
        case -1:
          break;
        case 1:
          return true;
          break;
      }

      if(unknown)
        return 0;
      else
        return -1;
    }
  }
  else if(src.id()==ID_not)
  {
    return -eval(src.op0());
  }
  else if(src.id()==ID_equal)
  {
    const exprt &op0=src.op0();
    const exprt &op1=src.op1();

    if(is_int(op0.type()) && is_int(op1.type()))
    {
      integer_intervalt itv1=eval_int_rec(op0);
      integer_intervalt itv2=eval_int_rec(op1);

      itv1.meet(itv2);

      if(itv1.is_bottom())
        return -1;
      else
      {
        if(itv1.lower_set && itv1.upper_set)
        {
          if(itv1.lower==itv1.upper)
            return 1;          
        }
         
        return 0;
      }
    }
    else if (is_float(op0.type()) && is_float(op1.type()))
    {

    }
  }
  else if(src.id()==ID_le)
  {
    std::cout << "ID_le" << std::endl;

    const exprt &op0=src.op0();
    const exprt &op1=src.op1();

    if(is_int(op0.type()) && is_int(op1.type()))
    {
      integer_intervalt itv1=eval_int_rec(op0);
      integer_intervalt itv2=eval_int_rec(op1);

      std::cout << "integer intervals " << std::endl;

      std::cout << "itv1 " << itv1.lower_set << " " << itv1.upper_set
                << " [" << itv1.lower << "," << itv1.upper << "]"
                << std::endl;

      std::cout << "itv2 " << itv2.lower_set << " " << itv2.upper_set
                << " [" << itv2.lower << "," << itv2.upper << "]"
                << std::endl;

      if(   itv1.upper_set 
         && itv2.lower_set
         && itv1.upper <= itv2.lower)
        return 1;
      else if( itv1.lower_set 
         && itv2.upper_set
         && itv1.lower > itv2.upper)
        return -1;
      else
        return 0;
    }

  }
  else if(src.id()==ID_ge)
  {
    const exprt &op0=src.op0();
    const exprt &op1=src.op1();

    exprt le_expr(binary_exprt(op1, ID_le, op0));

    return eval(le_expr);
  }
  else if(src.id()==ID_lt)
  {

  }

  return 0;
}


  
/*******************************************************************\

Function: interval_domt::eval_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

integer_intervalt interval_domt::eval_int_rec(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    const symbol_exprt &symbol=to_symbol_expr(src);

    int_mapt::const_iterator 
      it=int_map.find(symbol.get_identifier());

    if(it!=int_map.end())
    {
      return it->second;
    }
    else
    {
      return integer_intervalt();
    }
  } 
  else if(src.id()==ID_constant)
  {
    mp_integer val=0;
    if(!to_integer(src, val))
      return integer_intervalt(val);
  }


  return integer_intervalt(); 
}


/*******************************************************************\

Function: interval_domt::eval_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_float_intervalt interval_domt::eval_float_rec(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    const symbol_exprt &symbol=to_symbol_expr(src);

    float_mapt::const_iterator 
      it=float_map.find(symbol.get_identifier());

    if(it!=float_map.end())
    {
      return it->second;
    }
    else
    {
      return ieee_float_intervalt();
    }
  } 

  return ieee_float_intervalt();
}


/*******************************************************************\

Function: interval_domt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domt::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(int_mapt::const_iterator
      i_it=int_map.begin(); i_it!=int_map.end(); i_it++)
  {
    if(i_it->second.is_top()) continue;
    if(i_it->second.lower_set)
      out << i_it->second.lower << " <= ";
    out << i_it->first;
    if(i_it->second.upper_set)
      out << " <= " << i_it->second.lower;
    out << "\n";
  }

  for(float_mapt::const_iterator
      i_it=float_map.begin(); i_it!=float_map.end(); i_it++)
  {
    if(i_it->second.is_top()) continue;
    if(i_it->second.lower_set)
      out << i_it->second.lower << " <= ";
    out << i_it->first;
    if(i_it->second.upper_set)
      out << " <= " << i_it->second.lower;
    out << "\n";
  }
}


/*******************************************************************\

Function: interval_domt::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool interval_domt::merge(const interval_domt &b)
{
  bool result=false;
  
  for(int_mapt::iterator it=int_map.begin();
      it!=int_map.end(); ) // no it++
  {
    const int_mapt::const_iterator b_it=b.int_map.begin();
    if(b_it==b.int_map.end())
    {
      int_mapt::iterator next=it;
      next++; // will go away with C++11, as erase() returns next
      int_map.erase(it);
      it=next;
      result=true;
    }
    else
    {
      if(it->second.join(b_it->second))
        result=true;
        
      it++;
    }
  }

  for(float_mapt::iterator it=float_map.begin();
      it!=float_map.end(); ) // no it++
  {
    const float_mapt::const_iterator b_it=b.float_map.begin();
    if(b_it==b.float_map.end())
    {
      float_mapt::iterator next=it;
      next++; // will go away with C++11, as erase() returns next
      float_map.erase(it);
      it=next;
      result=true;
    }
    else
    {
      if(it->second.join(b_it->second))
        result=true;
        
      it++;
    }
  }

  return result;
}

/*******************************************************************\

Function: interval_domt::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domt::assign(const exprt &lhs, const exprt &rhs)
{
  havoc_rec(lhs);
  assume_rec(lhs, ID_equal, rhs);
}

/*******************************************************************\

Function: interval_domt::havoc_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domt::havoc_rec(const exprt &lhs)
{
  if(lhs.id()==ID_if)
  {
    havoc_rec(to_if_expr(lhs).true_case());
    havoc_rec(to_if_expr(lhs).false_case());
  }
  else if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();

    if(is_int(lhs.type()))
      int_map.erase(identifier);
    else if(is_float(lhs.type()))
      float_map.erase(identifier);
  }
  else if(lhs.id()==ID_typecast)
  {
    havoc_rec(to_typecast_expr(lhs).op());
  }
}

/*******************************************************************\

Function: interval_domt::assume_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domt::assume_rec(
  const exprt &lhs, irep_idt id, const exprt &rhs)
{
  if(lhs.id()==ID_typecast)
    return assume_rec(to_typecast_expr(lhs).op(), id, rhs);

  if(rhs.id()==ID_typecast)
    return assume_rec(lhs, id, to_typecast_expr(rhs).op());

  if(id==ID_equal)
  {
    assume_rec(lhs, ID_ge, rhs);
    assume_rec(lhs, ID_le, rhs);
    return;
  }
  
  if(id==ID_notequal)
  {
    return;
  }

  if(id==ID_ge)
    return assume_rec(rhs, ID_le, lhs);    
    
  if(id==ID_gt)
    return assume_rec(rhs, ID_lt, lhs);    
    
  // we now have lhs <  rhs or
  //             lhs <= rhs


  #ifdef DEBUG  
  std::cout << "assume_rec: " 
            << from_expr(lhs) << " " << id << " "
            << from_expr(rhs) << "\n";
  #endif

  assert(id==ID_lt || id==ID_le);

  
  if(lhs.id()==ID_symbol && rhs.id()==ID_constant)
  {
    irep_idt lhs_identifier=to_symbol_expr(lhs).get_identifier();
    
    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      mp_integer tmp;
      to_integer(rhs, tmp);
      if(id==ID_lt) --tmp;
      int_map[lhs_identifier].make_le_than(tmp);
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(rhs));
      if(id==ID_lt) tmp.decrement();
      float_map[lhs_identifier].make_le_than(tmp);
    }
  }
  else if(lhs.id()==ID_constant && rhs.id()==ID_symbol)
  {
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();
    
    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      mp_integer tmp;
      to_integer(lhs, tmp);
      if(id==ID_lt) ++tmp;
      int_map[rhs_identifier].make_ge_than(tmp);
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(lhs));
      if(id==ID_lt) tmp.increment();
      float_map[rhs_identifier].make_ge_than(tmp);
    }
  }
  else if(lhs.id()==ID_symbol && rhs.id()==ID_symbol)
  {
    irep_idt lhs_identifier=to_symbol_expr(lhs).get_identifier();
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();
    
    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      integer_intervalt &lhs_i=int_map[lhs_identifier];
      integer_intervalt &rhs_i=int_map[rhs_identifier];
      lhs_i.meet(rhs_i);
      rhs_i=lhs_i;
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_float_intervalt &lhs_i=float_map[lhs_identifier];
      ieee_float_intervalt &rhs_i=float_map[rhs_identifier];
      lhs_i.meet(rhs_i);
      rhs_i=lhs_i;
    }
  }
}

/*******************************************************************\

Function: interval_domt::assume_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domt::assume_rec(const exprt &cond, bool negation)
{
  if(cond.id()==ID_lt || cond.id()==ID_le ||
     cond.id()==ID_gt || cond.id()==ID_ge ||
     cond.id()==ID_equal || cond.id()==ID_notequal)
  {
    assert(cond.operands().size()==2);

    if(negation) // !x<y  ---> x>=y
    {
      if(cond.id()==ID_lt)
        assume_rec(cond.op0(), ID_ge, cond.op1());
      else if(cond.id()==ID_le)
        assume_rec(cond.op0(), ID_gt, cond.op1());
      else if(cond.id()==ID_gt)
        assume_rec(cond.op0(), ID_le, cond.op1());
      else if(cond.id()==ID_ge)
        assume_rec(cond.op0(), ID_lt, cond.op1());
      else if(cond.id()==ID_equal)
        assume_rec(cond.op0(), ID_notequal, cond.op1());
      else if(cond.id()==ID_notequal)
        assume_rec(cond.op0(), ID_equal, cond.op1());
    }
    else
      assume_rec(cond.op0(), cond.id(), cond.op1());
  }
  else if(cond.id()==ID_not)
  {
    assume_rec(to_not_expr(cond).op(), !negation);
  }
  else if(cond.id()==ID_and)
  {
    if(!negation)
      forall_operands(it, cond)
        assume_rec(*it, false);
  }
  else if(cond.id()==ID_or)
  {
    if(negation)
      forall_operands(it, cond)
        assume_rec(*it, true);
  }
}


/*******************************************************************\

Function: interval_domt::make_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt interval_domt::make_expression(const symbol_exprt &src) const
{
  if(is_int(src.type()))
  {
    int_mapt::const_iterator i_it=int_map.find(src.get_identifier());
    if(i_it==int_map.end()) return true_exprt();
    const integer_intervalt &interval=i_it->second;
    if(interval.is_top()) return true_exprt();
    if(interval.is_bottom()) return false_exprt();

    exprt::operandst conjuncts;

    if(interval.upper_set) 
    {
      exprt tmp=from_integer(interval.upper, src.type());
      conjuncts.push_back(binary_relation_exprt(src, ID_le, tmp));
    }

    if(interval.lower_set) 
    {
      exprt tmp=from_integer(interval.lower, src.type());
      conjuncts.push_back(binary_relation_exprt(tmp, ID_le, src));
    }
  
    return conjunction(conjuncts);
  }
  else if(is_float(src.type()))
  {
    float_mapt::const_iterator i_it=float_map.find(src.get_identifier());
    if(i_it==float_map.end()) return true_exprt();
    const ieee_float_intervalt &interval=i_it->second;
    if(interval.is_top()) return true_exprt();
    if(interval.is_bottom()) return false_exprt();

    exprt::operandst conjuncts;

    if(interval.upper_set) 
    {
      exprt tmp=interval.upper.to_expr();
      conjuncts.push_back(binary_relation_exprt(src, ID_le, tmp));
    }

    if(interval.lower_set) 
    {
      exprt tmp=interval.lower.to_expr();
      conjuncts.push_back(binary_relation_exprt(tmp, ID_le, src));
    }
  
    return conjunction(conjuncts);
  }
  else
    return true_exprt();
}
