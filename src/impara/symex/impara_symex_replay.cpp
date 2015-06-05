/*******************************************************************\

Module: Replaying a path from history

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/byte_operators.h>
#include <util/i2string.h>
#include <util/pointer_offset_size.h>
#include <util/expr_util.h>

#include <ansi-c/c_types.h>

#include <pointer-analysis/dereference.h>

#include "symex.h"
#include "../nodes.h"

#include "impara_symex_replay.h"


#include "symex_data_structures.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

struct replay_stept
{
  unsigned depth;
  unsigned from_thread;
  unsigned to_thread;
  bool branch_taken;
  loc_reft pc;
  
  replay_stept(unsigned _depth,
               unsigned _from_thread,
               unsigned _to_thread,
               bool _taken,
               loc_reft _pc) 
               : depth(_depth)
               , from_thread(_from_thread)
               , to_thread(_to_thread)
               , branch_taken(_taken)
               , pc(_pc) {}

  std::string pretty()
  {
    return i2string(depth) + " " 
         + i2string(from_thread) + " "
         + i2string(to_thread) + " "
         + (branch_taken ? "TAKEN" : "NOT TAKEN") + " "
         + i2string(pc.loc_number);
  }
  
};




typedef std::vector<replay_stept> replay_historyt;


void impara_symex_replay(
  statet &state,
  node_reft node_ref)
{

  #ifdef DEBUG
  std::cout << "impara_symex_replay " << node_ref->number << " " << state.node_ref->number<< std::endl;
  #endif

  if(node_ref == state.node_ref)
	  return;

  std::vector<node_reft> path;

  for(node_reft current=node_ref; current!=state.node_ref; --current)
  {
    path.push_back(current);
  }

  std::list<statet> further_states;

  unsigned thread=0;

  state.set_replay(true);

  bool branch_taken=false;

  for(int 
      i=path.size()-1;
      i>=0;
      --i)
  {
    const node_reft &current=path[i];
    assert(!current.is_nil());
     
    thread=current->thread_nr;
    
    if(path[i]->history->is_branch())
    {
      branch_taken=path[i]->history->is_branch_taken();
    } 
     
    state.set_current_thread(thread);

    if(state.get_instruction()->is_goto())
    {
      impara_symex_goto(state, branch_taken);
    } else
    {
      impara_symex(state, further_states);
    }
    
    state.node_ref=current;
  }
  
  #ifdef DEBUG
  state.output(std::cout);
  #endif

  state.set_replay(false);
  
  state.history=node_ref->history;

  assert(further_states.empty());  
}
