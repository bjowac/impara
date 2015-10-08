/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>
#include <memory>
#include <iostream>
#include <fstream>

#include <util/string2int.h>
#include <util/time_stopping.h>
#include <util/config.h>
#include <util/expr_util.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/graphml_goto_trace.h>

#include <analyses/goto_check.h>

#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/show_value_sets.h>

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <solvers/sat/satcheck.h>

#include "impara_parse_options.h"
#include "version.h"
#include "impara_path_search.h"

/*******************************************************************\

Function: impara_parse_optionst::impara_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

impara_parse_optionst::impara_parse_optionst(int argc, const char **argv):
  parse_options_baset(IMPARA_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  language_uit("IMPARA " IMPARA_VERSION, cmdline)
{
}
  
/*******************************************************************\

Function: impara_parse_optionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_parse_optionst::eval_verbosity()
{
  int v=8;
  
  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2int(cmdline.get_value("verbosity"));
    if(v<0)
      v=0;
    else if(v>9)
      v=9;
  }
  
  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: impara_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("all-properties"))
    options.set_option("all-properties", true);  

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);
  else
    options.set_option("simplify", true);

  if(cmdline.isset("no-cover"))
    options.set_option("cover", false);
  else
    options.set_option("cover", true);

  if(cmdline.isset("simple-force"))
    options.set_option("simple-force", true);
  else
    options.set_option("simple-force", false);

  if(cmdline.isset("strengthen"))
    options.set_option("strengthen", true);
  else
    options.set_option("strengthen", false);
    
  // magic error label
  if(cmdline.isset("strengthen-domain"))
    options.set_option("strengthen-domain", cmdline.get_value("strengthen-domain"));

  if(cmdline.isset("no-force"))
    options.set_option("force", false);
  else
    options.set_option("force", true);

  if(cmdline.isset("propagation"))
    options.set_option("propagation", true);
  else
    options.set_option("propagation", false);

  if(cmdline.isset("block"))
    options.set_option("block", true);
  else
    options.set_option("block", false);

  if(cmdline.isset("dpor"))
    options.set_option("dpor",true);
  else
    options.set_option("dpor",false);

  if(cmdline.isset("dpor-pointers"))
  {
	  options.set_option("dpor",true);
    options.set_option("dpor-pointers",true);
  }
  else
    options.set_option("dpor-pointers",false);

  if(cmdline.isset("no-POR"))
    options.set_option("POR",false);
  else
    options.set_option("POR",true);

  if(cmdline.isset("sleep"))
    options.set_option("sleep",true);
  else
    options.set_option("sleep",false);

  if(cmdline.isset("force-limit"))
    options.set_option("force-limit", cmdline.get_value("force-limit"));
  else
    options.set_option("force-limit", 2);

  if(cmdline.isset("cover-limit"))
    options.set_option("cover-limit", cmdline.get_value("cover-limit"));
  else
    options.set_option("cover-limit", 100000);

  if(cmdline.isset("bound"))
    options.set_option("bound", cmdline.get_value("bound"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("context-bound"))
    options.set_option("context-bound", cmdline.get_value("context-bound"));
      else
    options.set_option("context-bound",
      std::numeric_limits<int>::max());

  if(cmdline.isset("thread-limit"))
    options.set_option("thread-limit", cmdline.get_value("thread-limit"));
  else
    options.set_option("thread-limit", 
      std::numeric_limits<int>::max());

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("slice-by-trace"))
    options.set_option("slice-by-trace", cmdline.get_value("slice-by-trace"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // substitution previous expressions
  if(cmdline.isset("no-substitution"))
    options.set_option("substitution", false);
  else
    options.set_option("substitution", true);

  // check array bounds
  if(cmdline.isset("bounds-check"))
    options.set_option("bounds-check", true);
  else
    options.set_option("bounds-check", false);

  // check division by zero
  if(cmdline.isset("div-by-zero-check"))
    options.set_option("div-by-zero-check", true);
  else
    options.set_option("div-by-zero-check", false);

  // check overflow/underflow
  if(cmdline.isset("signed-overflow-check"))
    options.set_option("signed-overflow-check", true);
  else
    options.set_option("signed-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("unsigned-overflow-check"))
    options.set_option("unsigned-overflow-check", true);
  else
    options.set_option("unsigned-overflow-check", false);

  // check for NaN (not a number)
  if(cmdline.isset("nan-check"))
    options.set_option("nan-check", true);
  else
    options.set_option("nan-check", false);

  // check pointers
  if(cmdline.isset("pointer-check"))
    options.set_option("pointer-check", true);
  else
    options.set_option("pointer-check", false);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  // check overflow/underflow
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_value("error-label"));

  // generate unwinding assertions
  options.set_option("unwinding-assertions",
   !cmdline.isset("no-unwinding-assertions"));

  // generate unwinding assumptions otherwise
  options.set_option("partial-loops",
   cmdline.isset("partial-loops"));

  // remove unused equations
  options.set_option("slice-formula",
       cmdline.isset("slice-formula"));

  // simplify if conditions and branches
  if(cmdline.isset("no-simplify-if"))
    options.set_option("simplify-if", false);
  else
    options.set_option("simplify-if", true);

  if(cmdline.isset("arrays-uf-always"))
    options.set_option("arrays-uf", "always");
  else if(cmdline.isset("arrays-uf-never"))
    options.set_option("arrays-uf", "never");
  else
    options.set_option("arrays-uf", "auto");

  if(cmdline.isset("dimacs"))
    options.set_option("dimacs", true);

  if(cmdline.isset("refine"))
    options.set_option("refine", true);

  if(cmdline.isset("boolector"))
    options.set_option("boolector", true);

  if(cmdline.isset("cvc"))
    options.set_option("cvc", true);

  if(cmdline.isset("smt1"))
    options.set_option("smt1", true);

  if(cmdline.isset("smt2"))
    options.set_option("smt2", true);

  if(cmdline.isset("yices"))
    options.set_option("yices", true);

  if(cmdline.isset("z3"))
    options.set_option("z3", true);

  if(cmdline.isset("beautify-pbs"))
    options.set_option("beautify-pbs", true);

  if(cmdline.isset("beautify-greedy"))
    options.set_option("beautify-greedy", true);

  options.set_option("pretty-names", 
                     !cmdline.isset("no-pretty-names"));

  if(cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.get_value("outfile"));

  if(cmdline.isset("dot"))
    options.set_option("dot", cmdline.get_value("dot"));

  if(cmdline.isset("eager"))
    options.set_option("eager", true);

  if(cmdline.isset("forall-itp"))
    options.set_option("forall-itp", true);
  else
    options.set_option("forall-itp", true);

  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);

  if(cmdline.isset("bfs"))
    options.set_option("bfs", true);

  if(cmdline.isset("check-proof"))
    options.set_option("check-proof", true);
  else
    options.set_option("check-proof", false);

  if(cmdline.isset("node-limit"))
    options.set_option("node-limit", cmdline.get_value("node-limit"));
  else
    options.set_option("node-limit", 
      std::numeric_limits<int>::max());

  if(cmdline.isset("context-bound"))
    options.set_option("context-bound", cmdline.get_value("context-bound"));
  else
    options.set_option("context-bound", 
      std::numeric_limits<int>::max());

  if(cmdline.isset("unwind"))
    options.set_option("unwind-limit", cmdline.get_value("unwind"));
  else
    options.set_option("unwind-limit", 
      std::numeric_limits<int>::max());

  if(cmdline.isset("wordlevel-interpolation"))
  {
    options.set_option("wordlevel-interpolation", true);
  }
  else
  {
    options.set_option("wordlevel-interpolation", false);
  }


  if(cmdline.isset("graphml-cex"))
  {
    options.set_option("graphml-cex", cmdline.get_value("graphml-cex"));
    options.set_option("do-graphml-cex", true);
  }
  else
  {
    options.set_option("do-graphml-cex", false);
  }
}

/*******************************************************************\

Function: impara_parse_optionst::register_langauges

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void impara_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}

/*******************************************************************\

Function: impara_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int impara_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << IMPARA_VERSION << std::endl;
    return 0;
  }

  register_languages();

  // command line options

  optionst options;
  get_command_line_options(options);
  eval_verbosity();

  // get program

  goto_functionst goto_functions;

  if(get_goto_program(options, goto_functions))
    return 6;

  label_properties(goto_functions);

  if(cmdline.isset("show-properties"))
  {
    const namespacet ns(symbol_table);
    show_properties(ns, get_ui(), goto_functions);
    return 0;
  }
  
  // show it?
  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(get_ui(), goto_functions);
    return true;
  }

  if(set_properties(goto_functions))
    return 7;
    
  if(cmdline.isset("show-locs"))
  {
    const namespacet ns(symbol_table);
    locst locs(ns);
    locs.build(goto_functions);
    locs.output(std::cout);
    return 0;
  }



  // do actual analysis

  const namespacet ns(symbol_table);
  
  impara_path_searcht impara_path_search(options, ns, ui_message_handler);
  
  
  impara_path_search.do_cover=options.get_bool_option("cover");    

  if(!impara_path_search.do_cover)
  {
    impara_path_search.cover_limit=0;    
  }
  else
  {
    impara_path_search.cover_limit=options.get_signed_int_option("cover-limit");
  }

  impara_path_search.do_assertions=options.get_bool_option("assertions");    
  impara_path_search.do_force_cover=options.get_bool_option("force");    
  impara_path_search.do_propagation=options.get_bool_option("propagation");
  impara_path_search.do_simple_force=options.get_bool_option("simple-force");
  impara_path_search.do_strengthen=options.get_bool_option("strengthen");

  if(!impara_path_search.do_force_cover)
  {
    impara_path_search.force_limit=0;
  } else
  {
    impara_path_search.force_limit=options.get_signed_int_option("force-limit");
  }

  impara_path_search.thread_limit=options.get_unsigned_int_option("thread-limit");
  impara_path_search.context_bound=options.get_unsigned_int_option("context-bound");
  impara_path_search.do_dpor=options.get_bool_option("dpor");
  impara_path_search.do_por=options.get_bool_option("POR");
  impara_path_search.do_eager=options.get_bool_option("eager");
  impara_path_search.do_simplify=options.get_bool_option("simplify");
  impara_path_search.do_bfs=options.get_bool_option("bfs");
  impara_path_search.node_limit=options.get_signed_int_option("node-limit");
  impara_path_search.unwind_limit=options.get_signed_int_option("unwind-limit");
  impara_path_search.do_check_proof=options.get_signed_int_option("check-proof");
  impara_path_search.do_graphml_cex=options.get_bool_option("do-graphml-cex");

  switch(impara_path_search(goto_functions))
  {
  case safety_checkert::SAFE:
    report_properties(impara_path_search.property_map);
    report_success();
    return 0;
  
  case safety_checkert::UNSAFE:
    report_properties(impara_path_search.property_map);
  
    show_counterexample(impara_path_search.error_trace);    
    report_failure();
    
    if(impara_path_search.do_graphml_cex)
    {
      graphmlt graphml_cex;
      
      convert(ns, impara_path_search.error_trace, graphml_cex);
      
      std::string filename=options.get_option("graphml-cex");
      
      std::ofstream graphml_file(filename.c_str());
      write_graphml(graphml_cex, graphml_file);
    }
    
    return 10;
  
  default:
    report_properties(impara_path_search.property_map);
    report_error();  
    return 8;
  }
}

/*******************************************************************\

Function: impara_parse_optionst::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_parse_optionst::report_error()
{
  result() << "ERROR" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="ERROR";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}


/*******************************************************************\

Function: impara_parse_optionst::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_parse_optionst::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}


/*******************************************************************\

Function: impara_parse_optionst::show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_parse_optionst::show_counterexample(
  const goto_tracet &error_trace)
{
  const namespacet ns(symbol_table);

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    std::cout << std::endl << "Counterexample:" << std::endl;
    show_goto_trace(std::cout, ns, error_trace);
    break;
  
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, error_trace, xml);
      std::cout << xml << std::endl;
    }
    break;
  
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: impara_parse_optionst::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_parse_optionst::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: impara_parse_optionst::set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool impara_parse_optionst::set_properties(goto_functionst &goto_functions)
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_functions, cmdline.get_values("property"));  
  }

  catch(const char *e)
  {
    error() << e;
    return true;
  }

  catch(const std::string e)
  {
    error() << e;
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: impara_parse_optionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool impara_parse_optionst::get_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  if(cmdline.args.size()==0)
  {
    error() << "Please provide a program to verify" << eom;
    return true;
  }

  try
  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status() << "Reading GOTO program from file" << eom;

      if(read_goto_binary(cmdline.args[0],
           symbol_table, goto_functions, get_message_handler()))
        return true;
        
      config.ansi_c.set_from_symbol_table(symbol_table);

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }
      
      if(symbol_table.symbols.find(goto_functions.entry_point())==symbol_table.symbols.end())
      {
        error() << "The goto binary has no entry point; please complete linking" << eom;
        return true;
      }
    }
    else
    {
      if(parse()) return true;
      if(typecheck()) return true;
      if(final()) return true;

      // we no longer need any parse trees or language files
      clear_parse();

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

      if(symbol_table.symbols.find(goto_functions.entry_point())==symbol_table.symbols.end())
      {
        error() << "No entry point; please provide a main function" << eom;
        return true;
      }

      status() << "Generating GOTO Program" << eom;

      goto_convert(
        symbol_table, goto_functions, ui_message_handler);
    }



    if(process_goto_program(options, goto_functions))
      return true;
  }

  catch(const char *e)
  {
    error() << e;
    return true;
  }

  catch(const std::string e)
  {
    error() << e;
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: impara_parse_optionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool impara_parse_optionst::process_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  try
  {
    namespacet ns(symbol_table);

    // add the library
    status() << "Adding CPROVER library" << eom;
    link_to_library(
      symbol_table, goto_functions, ui_message_handler);

    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(
      symbol_table, goto_functions, cmdline.isset("pointer-check"));

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);
 
    // remove returns, gcc vectors, complex
    remove_returns(symbol_table, goto_functions);
    remove_vector(symbol_table, goto_functions);
    remove_complex(symbol_table, goto_functions);
    
    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(ns, options, goto_functions);

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(symbol_table);
  
    //remove unused functions
    remove_unused_functions(goto_functions, ui_message_handler);
  
    // recalculate numbers, etc.
    goto_functions.update();

    // add loop ids
    goto_functions.compute_loop_numbers();

    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      goto_functions.output(ns, std::cout);
      return true;
    }
  }

  catch(const char *e)
  {
    error() << e;
    return true;
  }

  catch(const std::string e)
  {
    error() << e;
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: impara_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void impara_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *          IMPARA " IMPARA_VERSION " - Copyright (C) 2011-2013           * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *      Oxford University, Computer Science Department     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " impara [-?] [-h] [--help]    show help\n"
    " impara file.c ...            source file names\n"
    "\n"
    "Frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    "\n"
    "Program instrumentation options:\n"
    " --bounds-check               enable array bounds checks\n"
    " --div-by-zero-check          enable division by zero checks\n"
    " --pointer-check              enable pointer checks\n"
    " --signed-overflow-check      enable arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n"
    " --nan-check                  check floating-point for NaN\n"
    " --show-properties            only show properties\n"
    " --show-loops                 show the loops in the program\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    "\n"
    "Verification options:\n"
    " --function name              set main function name\n"
    " --property nr                only check specific property\n"
    " --show-vcc                   print verification conditions\n"
    "\n"
    "Abstraction options:\n"
    " --no-force                   switch off force covers\n"
    " --force-limit                restrict force cover to at most <n> nodes (default 2)\n"
    " --no-POR                     switch off partial-order reduction\n"
    " --context-bound              limit number of context switches\n"
    " --word-level-interpolation   use wordlevel interpolation\n"
    "\n" 
    "Backend options:\n"
    " --beautify-greedy            beautify the counterexample (greedy heuristic)\n"
    " --smt1                       output subgoals in SMT1 syntax (experimental)\n"
    " --smt2                       output subgoals in SMT2 syntax (experimental)\n"
    " --boolector                  use Boolector (experimental)\n"
    " --cvc                        use CVC3 (experimental)\n"
    " --yices                      use Yices (experimental)\n"
    " --z3                         use Z3 (experimental)\n"
    " --refine                     use refinement procedure (experimental)\n"
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n"
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              stdio-XML interface\n"
    "\n";
}


/*******************************************************************\

Function: impara_parse_optionst::report_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_parse_optionst::report_properties(
  const impara_path_searcht::property_mapt &property_map)
{
  for(impara_path_searcht::property_mapt::const_iterator
      it=property_map.begin();
      it!=property_map.end();
      it++)
  {
    if(get_ui()==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(it->first));

      std::string status_string;

      switch(it->second.status)
      {
      case impara_path_searcht::PASS: 
        status_string="OK"; 
        break;
      case impara_path_searcht::FAIL: 
        status_string="FAILURE"; 
        break;
      case impara_path_searcht::NOT_REACHED: 
        status_string="OK: NOT REACHED"; 
        break;
      }

      xml_result.set_attribute("status", status_string);

      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << it->first << "] "
               << it->second.description << ": ";
      switch(it->second.status)
      {
      case impara_path_searcht::PASS: 
        status() << "OK";
        break;
      case impara_path_searcht::FAIL:
        status() << "FAILED"; 
        break;
      case impara_path_searcht::NOT_REACHED:
        status() << "OK: NOT REACHED"; 
        break;
      }
      status() << eom;
    }

    if(cmdline.isset("show-trace") &&
       it->second.status==impara_path_searcht::FAIL)
      show_counterexample(it->second.error_trace);
  }

  if(!cmdline.isset("property"))
  {
    status() << eom;

    unsigned failed=0;

    unsigned not_reached=0;

    for(impara_path_searcht::property_mapt::const_iterator
        it=property_map.begin();
        it!=property_map.end();
        it++)
    {
      if(it->second.status==impara_path_searcht::FAIL)
        failed++;
      if(it->second.status==impara_path_searcht::NOT_REACHED)
        not_reached++;
    }
    
    status() << "** " << failed << " failed, " << not_reached << " not reached of total " << property_map.size() << " properties"
             << eom;  
  }
}
