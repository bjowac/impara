/*******************************************************************\

Module: Computing shared accesses.

Author: Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/prefix.h>

#include "shared.h"

#include <pointer-analysis/dereference.h>

#include <iostream>

/*******************************************************************\

Function: sharedt::shared

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool sharedt::shared(const exprt& expr, sett& vars)
{
  try
  {
    exprt tmp=state.read_no_propagate(expr);
    
    return shared_rec(tmp, vars);
  } catch (...)
  {
    return false;
  }
}


/*******************************************************************\

Function: sharedt::shared_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool sharedt::shared_rec(const exprt& expr, sett& vars)
{
  bool result=false;

  if(expr.id()==ID_symbol)
  {
    if(!expr.get_bool(ID_C_SSA_symbol))
      return false;

    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    const irep_idt &identifier=symbol_expr.get(ID_C_full_identifier);

    const std::string id_string(id2string(identifier));

    // exclude thread id (symmetry argument)
    if(has_prefix(id_string, "__CPROVER_thread_id")
       || has_prefix(id_string, "__CPROVER_next_thread_id"))
    {
      return false;
    }
 
    impara_var_mapt::var_infot &var_info=
      state.var_map(identifier, "", expr.type());
    
    if(var_info.is_shared())
    {
      vars.insert(var_info.number);
      return true;
    }
  } 
  
  else if(false && expr.id()==ID_index)
  {
    sett vars_tmp;
  
    if(!shared_rec(expr.op0(), vars_tmp))
    {    
      return false;
    }

    exprt index=state.read(expr.op1());
    
    if(index.id()==ID_constant)
    {
      for(sett::const_iterator it=vars_tmp.begin();
          it!=vars_tmp.end();
          ++it)
      {
        std::string id=state.var_map.shared_id_vec[*it].c_str();
          
        id+=state.array_index_as_string(index);
      
        // TODO: refine here
      
        impara_var_mapt::var_infot &var_info=
          state.var_map(
            id, "", expr.type());

        vars.insert(var_info.number);            
      }
    }  
    else 
    {
      vars.insert(vars_tmp.begin(), vars_tmp.end());   
    }
    
    return true;
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

Function: sharedt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void sharedt::operator()(
	sett& reads, 
	sett& writes)
{
  const goto_programt::instructiont& instruction=*state.get_instruction();

  operator()(instruction, reads, writes);
}

void sharedt::operator()(
	const goto_programt::instructiont& instruction, 
	sett& reads, 
	sett& writes)
{
  switch(instruction.type)
  {  
    case ATOMIC_BEGIN:
	    {      
        for(goto_programt::const_targett 
            current=++state.get_instruction();
            current->type!=ATOMIC_END;
            current++)
        {
          if(current->type!=ATOMIC_END && current->type!=ATOMIC_BEGIN)
          {
            operator()(*current, reads, writes);
          }
        }
      }
      break;
    case FUNCTION_CALL:
      {
        const code_function_callt& function_call = to_code_function_call(instruction.code);
        const exprt::operandst &call_arguments=function_call.arguments();
    
        // check argumets
        for(unsigned i=0; i<call_arguments.size(); i++)
        { 
          shared(call_arguments[i], reads);
        }
      }
      break;

    case ASSUME:
      // effect like a write
      shared(instruction.guard, reads);
	    writes.insert(reads.begin(), reads.end()); 
      break;
    
    case ASSERT:
    case GOTO:
      shared(instruction.guard, reads);
      break;
    case ASSIGN:
      {
        const code_assignt &assign = to_code_assign(instruction.code);

        // read the address of the lhs, with propagation
        exprt lhs_address=state.read(address_of_exprt(assign.lhs()));
  
        // now SSA it, no propagation
        exprt lhs=dereference_exprt(lhs_address);

        // read the rhs
        exprt rhs=assign.rhs();

        shared(lhs, writes);
        shared(rhs, reads);
      }
      break;
    default:
      break;
  }
}
