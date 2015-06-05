#include "shared_step.h"


//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: shared_stept::intersect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool shared_stept::intersect(const shared_stept::sett& a, 
                             const shared_stept::sett& b)
{
  for(shared_stept::sett::const_iterator
	  it=a.begin();
	  it!=a.end();
	  ++it)
  {
    if(b.count(*it))
    {
#ifdef DEBUG
      std::cout << "intersection " << from_expr(*it) << std::endl;
#endif
      return true;
    }
  }

  return false;
}


/*******************************************************************\

Function: shared_stept::conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool shared_stept::conflict(const shared_stept::sett& reads1, const shared_stept::sett& writes1,
                            const shared_stept::sett& reads2, const shared_stept::sett& writes2)
{
  return intersect(writes1, writes2) || intersect(reads1, writes2) || intersect(reads2, writes1);
}


/*******************************************************************\

Function: shared_stept::shared_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool shared_stept::shared_rec(const exprt& expr, sett& vars)
{
  bool result=false;

  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    
    
    irep_idt identifier=symbol_expr.get_bool(ID_C_SSA_symbol) ? 
                          symbol_expr.get(ID_C_full_identifier)
                        : symbol_expr.get_identifier(); 

    if(identifier==irep_idt())
    {
      #ifdef DEBUG
      std::cout << "no identifier " << from_expr(var_map.ns, "", expr) << std::endl;
      #endif
      
      return false;
    }
 
    impara_var_mapt::var_infot &var_info=var_map(identifier, "", expr.type());
      
    if(var_info.is_shared())
    {
      vars.insert(symbol_exprt(identifier));
      return true;
    }
    else
    {
      #ifdef DEBUG
      std::cout << "not shared " << from_expr(var_map.ns, "", expr) << std::endl;
      #endif
    }
 
  } 
  else if(expr.id()==ID_address_of)
  {
    return false;
  }
  else
  {
    if(expr.has_operands())
      for(exprt::operandst::const_iterator 
          it=expr.operands().begin();
	        it!=expr.operands().end();
      	  ++it)
      {
        if(shared_rec(*it, vars))
    	  result=true;
      }
  }

  return result;
}

/*******************************************************************\

Function: shared_stept::output()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void shared_stept::output(const sett &set, std::ostream &out)
{
  out << "{";

  for(sett::iterator 
      it=set.begin();
      it!=set.end();
      ++it)
  {
    out << (it!=set.begin() ? "," : "") << from_expr(*it);
  }
  out << "}";
}

/*******************************************************************\

Function: shared_stept::output()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void shared_stept::output(const sett &reads, const sett &writes, std::ostream &out)
{
  out << "R=";
  output(reads, out);
  out << " , ";
 
  out << "W=";
  output(writes, out);
  out << std::endl;
}


bool has_pointer_expr(const namespacet &ns,
                      const exprt &src)
{
  if(src.id()==ID_symbol)
    return src.type().id()==ID_pointer;
  else
  {
    forall_operands(it, src)
      if(has_pointer_expr(ns, *it))
        return true;
  }
  
  return false;
}

bool has_pointer_assignment(
  const namespacet &ns,
  const exprt &lhs,
  const exprt &rhs)
{
  const typet &lhs_type=ns.follow(lhs.type());
  const typet &rhs_type=ns.follow(rhs.type());
 
  if(lhs_type.id()==ID_pointer || 
     rhs_type.id()==ID_pointer)
    return true;
  else
  if(rhs.id()==ID_with)
  {
    return has_pointer_expr(ns, rhs.op2());
  }

  return false;
}


/*******************************************************************\

Function: shared_stept::process_step()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shared_stept::process_step(const impara_stept &step, sett& reads, sett& writes)
{
  bool do_guard=!pointers_only || has_pointer_expr(var_map.ns, step.guard);
  bool do_assignment=!pointers_only || has_pointer_assignment(var_map.ns, step.ssa_lhs, step.ssa_rhs);

  if(do_guard)
  {
    if(locs[step.pc].target->is_assume())
      shared_rec(step.guard, writes);

    shared_rec(step.guard, reads);
  }

  if(do_assignment)
  {
    shared_rec(step.ssa_lhs, writes);
    shared_rec(step.ssa_rhs, reads); 
  }
  
  #ifdef DEBUG
  std::cout << "   do_guard " << from_expr(var_map.ns, "", step.guard) << "do_guard " << do_guard
            << "\n   do_assign " << from_expr(var_map.ns, "", step.ssa_lhs) 
            << "\n   do_assign " << do_assignment
            << " " << from_expr(var_map.ns, "", step.ssa_rhs) << std::endl;
  #endif
}

/*******************************************************************\

Function: shared_stept::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shared_stept::operator()(
	sett& reads, 
	sett& writes)
{
//  reads.clear();
//  writes.clear();

  if(step.is_atomic_end())
  {
    process_step(step, reads, writes);
    for(impara_step_reft s=step.predecessor;
        !s.is_nil() && !s->is_atomic_begin();
        --s)
    {
      process_step(*s, reads, writes);      
    }
  
  } 
  else
  {
    process_step(step, reads, writes);  
  }
}





