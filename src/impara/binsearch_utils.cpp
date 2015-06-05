#include <util/arith_tools.h>
#include <util/ieee_float.h>

#include <iostream>

#include "binsearch_utils.h"

constant_exprt between(const constant_exprt &lower, 
                       const constant_exprt &upper)
{
  if(lower.type()==upper.type() && 
     (lower.type().id()==ID_signedbv || lower.type().id()==ID_unsignedbv))
  {
    mp_integer vlower, vupper;
    to_integer(lower, vlower);
    to_integer(upper, vupper);
    assert(vupper>=vlower);
    if(vlower+1==vupper) return from_integer(vlower,lower.type()); //floor
    return from_integer((vupper+vlower)/2,lower.type());
  }
  if(lower.type().id()==ID_floatbv && upper.type().id()==ID_floatbv)
  {
    ieee_floatt vlower(to_constant_expr(lower));
    ieee_floatt vupper(to_constant_expr(upper));
    if(vlower.get_sign()==vupper.get_sign()) 
    {
      mp_integer plower = vlower.pack(); //compute "median" float number
      mp_integer pupper = vupper.pack();
      //assert(pupper>=plower);
      ieee_floatt res;
      res.unpack((plower+pupper)/2); //...by computing integer mean
      return res.to_expr();
    }
    ieee_floatt res;
    res.make_zero();
    return res.to_expr();
  }
  assert(false); //types do not match or are not supported
}


bool less_than(const constant_exprt &v1, const constant_exprt &v2)
{
  if(v1.type()==v2.type() && 
     (v1.type().id()==ID_signedbv || v1.type().id()==ID_unsignedbv))
  {
    mp_integer vv1, vv2;
    to_integer(v1, vv1);
    to_integer(v2, vv2);
    return vv1<vv2;
  }
  if(v1.type().id()==ID_floatbv && v2.type().id()==ID_floatbv)
  {
    ieee_floatt vv1(to_constant_expr(v1));
    ieee_floatt vv2(to_constant_expr(v2));
    return vv1<vv2;
  }

  std::cout << v1 << " " << v2 << std::endl;

  assert(false); //types do not match or are not supported
}

/*******************************************************************\

Function: template_domaint::get_max_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt get_max_value(
  const typet &type)
{
  if(type.id()==ID_signedbv)
  {
    return to_signedbv_type(type).largest_expr();
  }
  if(type.id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(type).largest_expr();
  }
  if(type.id()==ID_floatbv) 
  {
    ieee_floatt max;
    max.make_fltmax();
    return max.to_expr();
  }
  assert(false); //type not supported
}

/*******************************************************************\

Function: template_domaint::get_min_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt get_min_value(
  const typet &type)
{

  if(type.id()==ID_signedbv)
  {
    return to_signedbv_type(type).smallest_expr();
  }
  if(type.id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(type).smallest_expr();
  }
  if(type.id()==ID_floatbv) 
  {
    ieee_floatt min;
    min.make_fltmin();
    return min.to_expr();
  }
  assert(false); //type not supported
}

