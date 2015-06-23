/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_PARSEOPTIONS_H
#define CPROVER_IMPARA_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>
#include <util/options.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/safety_checker.h>
#include <langapi/language_ui.h>
#include <cbmc/xml_interface.h>

#include "impara_path_search.h"

#define IMPARA_OPTIONS \
  "(all-properties)" \
  "(arch):" \
  "(function):" \
  "(debug-level):" \
  "D:I:(node-limit):" \
  "(slice)(eager)"\
  "(xml-ui)(xml-interface)(vcd):" \
  "(interpol):(forall-itp)"\
  "(cvc)(smt1)(smt2)(boolector)(yices)(z3)(opensmt)" \
  "(show-loops)(show-vcc)(no-simplify)(no-cover)"\
  "(simple-force)(no-force)(force-limit):(cover-limit):"\
  "(propagation)(strengthen)(strengthen-domain):"\
  "(sleep)(no-POR)(bfs)(dpor)(dpor-pointers)(max-threads):(depth):(context-bound):(unwind):" \
  "(bounds-check)(div-by-zero-check)(pointer-check)" \
  "(signed-overflow-check)(unsigned-overflow-check)(nan-check)" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(svcomp)(graphml-cex):" \
  "(little-endian)(big-endian)" \
  "(show-properties)(property):" \
  "(show-locs)(show-goto-functions)(show-value-sets)" \
  "(error-label):(verbosity):(version)" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)" \
  "(ppc-macos)(no-arch)" \
  "(no-assertions)"\
  "(dot):(check-proof)"


class impara_parse_optionst:
  public parse_options_baset,
  public xml_interfacet,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  impara_parse_optionst(int argc, const char **argv);
  virtual ~impara_parse_optionst(){}

protected:
  virtual void register_languages();

  virtual void get_command_line_options(optionst &options);

  virtual bool get_goto_program(
    const optionst &options,
    goto_functionst &goto_functions);

  virtual bool process_goto_program(
    const optionst &options,
    goto_functionst &goto_functions);
    
  bool set_properties(goto_functionst &goto_functions);
  
  void eval_verbosity();
  
  void report_success();

  void report_failure();

  void report_error();
  
  void show_counterexample(
    const goto_tracet &error_trace);
  
  void report_properties(const impara_path_searcht::property_mapt &);
};

#endif
