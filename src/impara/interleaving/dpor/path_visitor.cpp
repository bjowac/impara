#include <cassert>
#include <string>
#include <algorithm>

#include <util/replace_expr.h>

#include <util/std_expr.h>
#include <symex/var_map.h>
#include <path-symex/locs.h>

#include "path_visitor.h"
#include "symex/state.h"
#include "nodes.h"

#include "../utility/shared_step.h"



//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

struct recordt 
{
	impara_step_reft step_ref;
	unsigned depth;
	std::set<unsigned> visited;
};


typedef std::vector<recordt> stackt;

void print_path(path_visitort::patht &path)
{
  std::cout << "path_visitort: path ";
  for(unsigned i=0; i<path.size(); ++i)
  {
    std::cout << "N"<<path[i]->node_ref->number 
	      << "@"<<path[i]->thread_nr
              <<  " ";
  }
  std::cout<< std::endl;
}
/*
Function:forall_prefixes (node_reft terminal,  path_visitort &visitor)
Input: A node [it can be a leaf or non-leaf]
Output: 
 */
void forall_prefixes
  (node_reft terminal,
   path_visitort &visitor)
{
  stackt stack;
  
  typedef path_visitort::patht patht;

  if(terminal.is_nil())
   return;

  patht path;

  unsigned depth=0;

  unsigned paths=0;

  stack.resize(1);
  stack[0].step_ref=terminal->history;
  stack[0].depth=0;

#if 0
  for(unsigned i=0; i<terminal->cover.size(); ++i)
  {
    const node_reft covered_node=terminal->cover[i];
    recordt b;
    b.depth=0;
    b.step_ref=covered_node->history;
    stack.push_back(b);      
  }
#endif

  impara_step_reft s;

  //std::set<unsigned> visited;

  while(!stack.empty())
  {
    // get top element
    {
      const recordt &b=stack.back();
      s=b.step_ref;
      depth=b.depth;
      //visited=b.visited;
    }
    
    stack.pop_back();

    /*
    unsigned index=s.get_index();
    
    if(visited.count(index))
    {
      #ifdef DEBUG
      std::cout << "path rejected at " << s->node_ref->number << std::endl;
      print_path(path);
      #endif
      continue;
    }

    visited.insert(index);
    */     

    path.resize(depth);


    for (impara_step_reft 
       step_ref(s); 
       !step_ref.is_nil();
       --step_ref, ++depth)
    {
      path.push_back(step_ref);

      node_reft node_ref=step_ref->node_ref;

      if(node_ref.is_nil())
        break;
	  
#if 0
      for(unsigned i=0; i<node.cover.size(); ++i)
      {
        const node_reft covered_node=node.cover[i];
        recordt b;
        b.depth=depth+1;
        b.step_ref=covered_node->history;
        b.visited=visited;
        stack.push_back(b);      
      }
#endif
    }

	#ifdef DEBUG
	print_path(path);
	#endif

    visitor(path, terminal);
    ++paths;
  }
 
  #ifdef DEBUG
  std::cout << "Paths visited " << paths << " for " << terminal->number << std::endl;
  #endif
}

void forall_prefixes_through
  (node_reft terminal,
   path_visitort &visitor,
   node_reft through)
{

	stackt stack;

	typedef path_visitort::patht patht;

  if(terminal.is_nil())
   return;

  patht path;

  unsigned depth=0;

  unsigned paths=0;

  stack.resize(1);
  stack[0].step_ref=terminal->history;
  stack[0].depth=0;

  for(unsigned i=0; i<terminal->cover.size(); ++i)
  {
    const node_reft covered_node=terminal->cover[i];
    recordt b;
    b.depth=0;
    b.step_ref=covered_node->history;
    stack.push_back(b);      
  }

  impara_step_reft s;

	std::set<unsigned> visited;

  while(!stack.empty())
  {
    // get top element
    {
      const recordt &b=stack.back();
      s=b.step_ref;
      depth=b.depth;
      visited=b.visited;
    }
    
    stack.pop_back();

    unsigned index=s.get_index();
    
    if(visited.count(index))
	  {
	  	#ifdef DEBUG
	  	std::cout << "path rejected at " << s->node_ref->number << std::endl;
			print_path(path);
			#endif
	    continue;
	  }

	  visited.insert(index);
     
    path.resize(depth);

    for (impara_step_reft 
       step_ref(s); 
       !step_ref.is_nil();
       --step_ref, ++depth)
    {
      path.push_back(step_ref);

      node_reft node_ref=step_ref->node_ref;

      if(node_ref.is_nil())
        continue;

      nodet &node=*node_ref;

			bool going_through=false;
			
      for(unsigned i=0; i<node.cover.size(); ++i)
      {
        const node_reft covered_node=node.cover[i];				
				going_through=(through==covered_node);
      }
			
			if(going_through)
			{
        recordt b;
        b.depth=depth+1;
        b.step_ref=through->history;
        b.visited=visited;
        stack.push_back(b);   
			}
			else
      for(unsigned i=0; i<node.cover.size(); ++i)
      {
        const node_reft covered_node=node.cover[i];
        recordt b;
        b.depth=depth+1;
        b.step_ref=covered_node->history;
        b.visited=visited;
        stack.push_back(b);      
      }
    }

		#ifdef DEBUG
		print_path(path);
		#endif


    visitor(path, terminal);

    ++paths;
  }
 
  #ifdef DEBUG
  std::cout << "Paths visited " << paths << std::endl;
  #endif
}


