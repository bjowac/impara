/*******************************************************************\

Module: Variable Numbering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol.h>
#include <util/std_expr.h>
#include <util/prefix.h>

#include "var_map.h"

//#define DEBUG

#include <iostream>

/*******************************************************************\

Function: impara_var_mapt::var_infot::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_var_mapt::var_infot::output(std::ostream &out) const
{
  out << "full_identifier: " << id2string(full_identifier) << "\n";
  out << "symbol: " << symbol << "\n";
  out << "suffix: " << suffix << "\n";

  out << "kind: ";
  kind.output(out);
  
  out << "\n";
  
  out << "number: " << number << "\n";
  
  out << "\n";
}


void impara_var_mapt::var_infot::kindt::output(std::ostream &out) const
{
  switch(kind_enum)
  {
  case PROCEDURE_LOCAL: out << "PROCEDURE_LOCAL"; break;
  case THREAD_LOCAL: out << "THREAD_LOCAL"; break;
  case SHARED: out << "SHARED"; break;
  }
}


/*******************************************************************\

Function: impara_var_mapt::kind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

impara_var_mapt::var_infot::kindt::kindt(const irep_idt &symbol_irep, const namespacet &ns)
{

  if(has_prefix(id2string(symbol_irep), "symex::nondet"))
  {
    kind_enum=THREAD_LOCAL;
  }
  else if(has_prefix(id2string(symbol_irep), "symex_dynamic::"))
  {
    kind_enum=SHARED;
  }
  else
  {
    try
    {

      const std::string identifier=id2string(symbol_irep);
      std::size_t pos_at=identifier.find('@');

      const symbolt &symbol=ns.lookup(identifier.substr(0,pos_at));

      if(symbol.is_static_lifetime)
      {
        if(symbol.is_thread_local)
          kind_enum=THREAD_LOCAL;
        else
          kind_enum=SHARED;
      }
      else
        kind_enum=PROCEDURE_LOCAL;
    }
    
    catch(std::string s)
    {
      throw "impara_var_mapt::init identifier \"" +
            id2string(symbol_irep)+
            "\" lookup in ns failed";
    }
  }
}


/*******************************************************************\

Function: impara_var_mapt::init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_var_mapt::init(var_infot &var_info)
{
  if(var_info.is_shared())
    var_info.number=shared_count++;
  else
    var_info.number=local_count++;
}

/*******************************************************************\

Function: impara_var_mapt::var_infot::ssa_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt impara_var_mapt::var_infot::ssa_identifier
  (unsigned thread, 
   unsigned counter) const
{

  const std::string id_string=id2string(full_identifier);
  std::size_t pos_at=id_string.find('@');

  return id_string.substr(0, pos_at)
         +(!kind.is_shared() && thread>0 ? "@"+std::to_string(thread) : "")
         + "#"+std::to_string(counter);
}

/*******************************************************************\

Function: impara_var_mapt::operator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

impara_var_mapt::var_infot &impara_var_mapt::operator()(
  const irep_idt &symbol,
  const irep_idt &suffix,
  const typet &type)
{
  std::string full_identifier=
    id2string(symbol)                                // symbol
   +id2string(suffix);                               // suffix
    
  #ifdef DEBUG
  std::cout << "impara_var_map::operator(): " << full_identifier << std::endl;
  #endif   

  std::pair<id_mapt::iterator, bool> result;

  result=id_map.insert(std::pair<irep_idt, var_infot>(
    full_identifier, var_infot()));
  
  if(result.second) // inserted?
  {
    var_infot::kindt kind(symbol, ns);
    result.first->second.kind=kind;
    result.first->second.full_identifier=full_identifier;
    result.first->second.symbol=symbol;
    result.first->second.suffix=suffix;
    result.first->second.type=type;
    init(result.first->second);
    if(result.first->second.is_shared())
    {
      shared_id_vec.push_back(full_identifier);
    }
  } else
  {
    #ifdef DEBUG
    std::cout << "impara_var_map::operator(): Already inserted " << std::endl;
    #endif
  }
    
  return result.first->second;
}

impara_var_mapt::var_infot&
impara_var_mapt::operator[]
  (const irep_idt &full_identifier)
{
  id_mapt::iterator it=id_map.find(full_identifier);

  if(it==id_map.end())
  {
    return dummy;
  }
  else
  {
    return it->second;
  }
}
