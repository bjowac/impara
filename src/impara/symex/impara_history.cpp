/*******************************************************************\

Module: History of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/decision_procedure.h>
#include <util/i2string.h>
#include <util/find_symbols.h>
#include <util/replace_expr.h>
#include <solvers/prop/prop_conv.h>

#include <langapi/language_util.h>

#include <algorithm>
#include <set>
#include <path-symex/locs.h>


#include "impara_history.h"

#include "from_ssa.h"

#include <symex/state.h>
#include "../nodes.h" // NOTE: remove for CPROVER main branch

#include "../simple_checker.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: statet::show_vcc

  Inputs: show verification condition

 Outputs:

 Purpose:

\*******************************************************************/

std::string impara_step_reft::pretty(
  const namespacet &ns, 
  const exprt &expr) const
{
  std::string result;

  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      result += "  " + from_expr(ns, "", *it) + "\n"; 
  }
  else {
    result+="  " + from_expr(ns, "", expr) + "\n"; 
  }
  
  return result;
}

/*******************************************************************\

Function: statet::show_vcc

  Inputs: show verification condition

 Outputs:

 Purpose:

\*******************************************************************/

void impara_step_reft::output(
  const namespacet &ns,
  const locst &locs,
  class propagationt &propagation,
  node_reft ancestor,
  const exprt& start, 
  const exprt& cond,
  std::ostream &out) const
{
  bool reached_ancestor= ancestor.is_nil();

  std::string s;

  unsigned step_nr=0;

  // determine nr of steps
  for(impara_step_reft h(*this); !h.is_nil();--h)
  {
    ++step_nr;
  }
  
  unsigned start_nr=step_nr; 
  
  // print the constraints
  for(impara_step_reft h(*this); !h.is_nil();--h, --start_nr)
  {
    std::string current_step;

    const impara_stept &step=*h;


    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) {
      break;
    }

    current_step=step.pretty(ns, locs, propagation, start_nr);

    if(current_step.size())
    {
      s= current_step + "\n"+ s;
    }
  }

  if(!start.is_true())
  {
    s= "   {"+i2string(start_nr)
         +"}: N" 
         + i2string(ancestor->number) + " " 
         + pretty(ns, start) 
         + "\n\n"+s;
  }

  
  s+= "|--------------------------\n"; 

  ++step_nr;

  s+= "{"+ i2string(step_nr) + "} " 
    + "N" + i2string((*this)->node_ref->number) + " " 
    + pretty(ns, cond) 
    + " ~> " + from_expr(ns, "", propagation(cond))
    + "\n";
   
  out << s;
}


/*******************************************************************\

Function: impara_step_reft::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt impara_step_reft::rename(
	const exprt &src, node_reft ancestor) const
{
  if(src.is_true() || src.is_false())
    return src;

  exprt result(src);

  typedef hash_set_cont<irep_idt, irep_id_hash> symbol_sett;
  symbol_sett depends;

  find_symbols(src,depends);
 
  replace_mapt replace_map;

  
  assert(!ancestor.is_nil());

  // replace the symbols in src by the suitable SSA assignments
  for(impara_step_reft h(ancestor->history); !h.is_nil() &&!depends.empty();--h)
  {
    const impara_stept& step=*h;

      
    if(step.full_lhs.is_not_nil())
    {
      const symbol_exprt &id=to_symbol_expr(step.full_lhs);
      std::string identifier=
        id2string(to_symbol_expr(id).get_identifier());
      std::size_t pos_sharp=identifier.rfind('#');
      identifier=identifier.substr(0, pos_sharp);
      
      symbol_sett::iterator 
        s_it=depends.find(identifier);

      if(s_it!=depends.end())
      {
   	    // remove symbol from depends
    	  depends.erase(s_it);
      
    	  // replace the expression in src
        exprt lhs=from_ssa(step.full_lhs);
     	  replace_map[lhs]=step.ssa_lhs;
      }
    }
  }

  replace_expr(replace_map, result);

  return result;
}



/*******************************************************************\

Function: impara_step_reft::cone

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_step_reft::cone(const exprt &src, 
                            impara_step_reft until,
                            std::set<exprt> &result)
{
  if(src.is_true() || src.is_false())
    return;

  find_symbols(src, result);

  // replace the symbols in src by the suitable SSA assignments
  for(impara_step_reft h(*this); until<h && !h.is_nil();--h)
  {
    const impara_stept& step=*h;
    
    if(step.full_lhs.is_not_nil())
    {
      exprt lhs=from_ssa(step.full_lhs);

      std::set<exprt>::iterator 
        s_it=result.find(lhs);
      
      if(s_it!=result.end())
      {
       	find_symbols(from_ssa(step.ssa_rhs), result);
      }
    }
  }
}

/*******************************************************************\

Function: impara_step_reft::cone

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


/*******************************************************************\

Function: impara_historyt::writes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_step_reft::writes(impara_step_reft until,
                              std::set<exprt> &result)
{
  // replace the symbols in src by the suitable SSA assignments
  for(impara_step_reft h(*this); until<h && !h.is_nil();--h)
  {
    const impara_stept& step=*h;
    
    if(step.full_lhs.is_not_nil())
    {
      exprt lhs=from_ssa(step.full_lhs);

      result.insert(lhs);
    }
  }
}

/*******************************************************************\

Function: impara_historyt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_step_reft::convert(class prop_convt &dest, 
            node_reft ancestor)
{
  bool reached_ancestor=false;

  int i=0; // counter for debugging purposes

  for(impara_step_reft h(*this); !h.is_nil();--h)
  {
    impara_stept &step=*h;
    
    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) return;
    
    if( step.guard.is_not_nil())
    {
      ++i;
    }

    if(step.full_lhs.is_not_nil())
      ++i;

    const exprt& guard = step.guard;
    const exprt& lhs   = step.ssa_lhs;
    const exprt& rhs   = step.ssa_rhs;

    try {

      if(guard.is_not_nil() &&
         !guard.is_true())
      {
        dest.set_to(guard, true);
      }      

    }
    catch (std::string &s)
    {
      throw "statet::ssa_constraints: " + (step.guard.is_nil() ? "" : from_expr(step.guard) ) +  " : " + s; 
    }
   
    catch (char const* c)
    {
      std::string s(c);
      throw "statet::ssa_constraints: " + (step.guard.is_nil() ? "" : from_expr(step.guard) + " -> ") + " : " + s; 
    }

    try
    {

      if(step.full_lhs.is_not_nil())
      {
        dest.set_to(equal_exprt(lhs, rhs.is_nil() ? lhs : rhs), true);
      }
    }

    catch (std::string &s)
    {
      throw "statet::ssa_constraints: " + lhs.pretty(2) + "\n:=\n" + rhs.pretty(2) + " : " + s; 
    }
   
    catch (char const* c)
    {
      std::string s(c);
      throw "statet::ssa_constraints: " + lhs.pretty(2) + "\n:=\n" + rhs.pretty(2);  + " : " + s; 
    }

  }
}


void impara_step_reft::get_core_steps(class prop_convt &dest, 
            std::vector<literalt>& literals,
            std::vector<impara_step_reft>& steps)
{

  unsigned nr=0;

  for(impara_step_reft step : steps)
  {
    const literalt& literal=literals[nr];

    if(  literal.is_constant() 
	    || !dest.is_in_conflict(literal)
	    )
    {
      step->set_hidden();
    } 
    ++nr;
  }
}


/*******************************************************************\

Function: impara_historyt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_step_reft::convert(
            class prop_convt &dest, 
            node_reft ancestor,
            propagationt &propagation,
            std::vector<literalt>& literals,
            std::vector<exprt>& lazy,
            std::vector<impara_step_reft> &steps)
{
  bool reached_ancestor=false;

  int i=0; // counter for debugging purposes

  std::vector<exprt> eager;

  for(impara_step_reft h(*this); !h.is_nil();--h)
  {
    impara_stept &step=*h;

    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) return;

    if( step.guard.is_not_nil())
    {
      ++i;
    }

    const exprt& full_lhs   = step.full_lhs;

    if(full_lhs.is_not_nil())
      ++i;

    if(step.is_hidden()) continue;

    const exprt& guard = step.guard;
    const exprt& lhs   = step.ssa_lhs;
    const exprt& rhs   = step.ssa_rhs;

    try {

      exprt prop_guard=propagation(guard);

      if(prop_guard.is_not_nil() &&
         !prop_guard.is_true())
      {
        literals.push_back(dest(prop_guard));
        if(!literals.back().is_constant())
          dest.set_frozen(literals.back());
        lazy.push_back(prop_guard);
        steps.push_back(h);
      }
    }
    catch (std::string &s)
    {
      throw "statet::ssa_constraints: guard " + s + "\n"
          + (step.guard.is_nil() ? "" : step.guard.pretty());
    }

    catch (char const* c)
    {
      std::string s(c);
      throw "statet::ssa_constraints: guard " + s + "\n"
          + (step.guard.is_nil() ? "" : step.guard.pretty());
    }

    try
    {
      if(full_lhs.is_not_nil())
      {
        exprt equality=equal_exprt(lhs, rhs.is_nil() ? lhs : propagation(rhs));

        find_symbols_sett symbols;
        find_symbols(rhs, symbols);

      
        if(full_lhs.type().has_subtype()
           && symbols.size()>0)
        {
          literals.push_back(dest(equality));
          if(!literals.back().is_constant())
            dest.set_frozen(literals.back());
          lazy.push_back(equality);
          steps.push_back(h);
        }
        else
        { 
          eager.push_back(equality);
        }
      }

    }

    catch (std::string &s)
    {
      throw "statet::ssa_constraints: assignment " + s + "\n" + lhs.pretty(2) + "\n:=\n" + rhs.pretty(2);
    }

    catch (char const* c)
    {
      std::string s(c);
      throw "statet::ssa_constraints: assignment " + s + "\n" + lhs.pretty(2) + "\n:=\n" + rhs.pretty(2);
    }

  }
  
  for(const exprt &expr : eager)
    dest.set_to_true(expr);
}


/*******************************************************************\

Function: impara_historyt::step_reft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string impara_stept::pretty(const namespacet &ns, 
                     const locst &locs,
                     class propagationt &propagation,
                     int step_nr) const
{
  std::string current_step;

  #if 0
  if(is_hidden())
    return "";
  #endif

  std::string indent=(is_hidden())? "//  " : "";


  std::string step_str;
  step_str+= indent
          + (step_nr > 0 ? ( "{" + i2string(step_nr) + "}   ") : "")
          + " N=" + i2string(node_ref->number) + (node_ref->has_label() ? "L" : "U")
          + " T=" + i2string(thread_nr) 
          + " PC=" + i2string(pc.loc_number)
          + " " + (is_atomic() ? "ATOMIC" : "")
          + " " + (is_atomic_end() ? "ATOMIC_END" : "");
  current_step += step_str;
      
  if( guard.is_not_nil())
  {
    exprt guard_prop=propagation(guard, true);
    
    std::string guard_str="[" + from_expr(ns, "", guard) + "]";
    
    if(guard!=guard_prop)
      guard_str+=" ~> [" + from_expr(ns, "", guard_prop) + "]";
    
    from_expr(ns, "", guard_prop);
    
  
    current_step +=guard_str ;
  }

  if(full_lhs.is_not_nil())
  {
    std::string constraint;

    std::string assign=" := ";
    if(ns.follow(full_lhs.type()).id()==ID_pointer)
      assign=" => ";
    
    if(ssa_rhs.id()==ID_array && ssa_rhs.operands().size()>10)
    {
      constraint=from_expr(ns, "", ssa_lhs) + assign + "{...}";
    }
    else if(ssa_rhs.is_nil())
      constraint=from_expr(ns, "", ssa_lhs) 
                +assign +from_expr(ns, "", ssa_lhs);
    else {
      exprt rhs_prop=propagation(ssa_rhs, true);
      std::string rhs_str=from_expr(ns, "", ssa_rhs);
      
      if(ssa_rhs!=rhs_prop)
        rhs_str+=" ~> " + from_expr(ns, "", rhs_prop);
    
      
      constraint=
                id2string(to_symbol_expr(ssa_lhs).get_identifier())
                + assign 
                + rhs_str ;
    }

    if(constraint!="")
      current_step += constraint;
  }

  return current_step;
}


void impara_step_reft::get_symbols(
              std::set<exprt> &input,
              replace_mapt &vars, // pre_state -> post_state
              node_reft ancestor)
{
  bool reached_ancestor=false;


  std::set<symbol_exprt> lhs; // variables used
  std::set<symbol_exprt> rhs; // variables modified

  for(impara_step_reft h(*this); !h.is_nil();--h)
  {
    impara_stept &step=*h;
    
    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) break;

    find_symbols(step.ssa_rhs, rhs);
    find_symbols(step.ssa_lhs, lhs);
    find_symbols(step.guard, rhs);
  }

  replace_mapt lhs_map;

  from_ssa(lhs, lhs_map);

  replace_mapt rhs_map;

  from_ssa(rhs, rhs_map);

  for(replace_mapt::iterator
      it=rhs_map.begin();
      it!=rhs_map.end();
      ++it)
  {
    const exprt &rhs_var=it->first;
    const exprt &rhs_ssa_var=it->second;

    replace_mapt::iterator it2=lhs_map.find(rhs_var);

    if(it2!=lhs_map.end())
    {
      const exprt &lhs_ssa_var=it2->second;

      vars[rhs_ssa_var]=lhs_ssa_var;
    }
  }
  
  std::set_difference(rhs.begin(), rhs.end(), lhs.begin(), lhs.end(),
    std::inserter(input, input.end()));
}

unsigned impara_step_reft::get_distance(node_reft ancestor)
{
  unsigned result=0; 

  bool reached_ancestor=false;

  for(impara_step_reft h(*this); !h.is_nil();--h)
  {
    impara_stept &step=*h;
    
    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) break;

    ++result;
  }
  return result;
}




