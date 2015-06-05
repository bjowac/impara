#include <util/prefix.h>

#include "from_ssa.h"


/*******************************************************************\

Function: from_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt from_ssa(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    std::string identifier=id2string(to_symbol_expr(src).get_identifier());
    
    if(has_prefix(id2string(identifier), "symex::nondet"))
    	return src;
    
    std::size_t pos_sharp=identifier.rfind('#');
    if(pos_sharp==std::string::npos) return src;    
    
    return symbol_exprt(identifier.substr(0,pos_sharp), src.type());
  }
  
  if(src.has_operands())
  {
    exprt tmp=src;
  
    Forall_operands(it, tmp)
    {
      exprt tmp2=from_ssa(*it);
      *it=tmp2;
    }
    
    return tmp;
  }
  
  return src;
}


void from_ssa(const std::set<symbol_exprt> &in,
                       replace_mapt &out)
  {
    for(std::set<symbol_exprt>::const_iterator
        it=in.begin();
        it!=in.end();
        ++it) 
    {
      exprt o_symbol(from_ssa(*it));
      
      // record the first occurs
      if(out.find(o_symbol)==out.end())
        out[o_symbol]=*it;
    }
  }



