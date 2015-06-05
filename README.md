
What is Impara?

Impara is a software model checker for multi-threaded C programs with POSIX and WIN 32 threads.
Build instructions

1. Obtain CBMC (tested SVN version 4789):

svn co -r4789 http://www.cpurover.org/svn/cbmc/trunk cbmc

2. Obtain Impara from the svn:

svn co http://www.cprover.org/svn/software/impara/

3. Set the path to CBMC in the Impara config file. For this, please modify variable CBMC in file:

impara/trunk/src/config.template

copy the file to impara/trunk/src/config.

4. Run make in directory impara/trunk/src
Command-line options

–error-label ERROR

This defines the error location, whose reachability Impara should check. The options is required to run SVCOMP benchmarks.

–eager

Tells Impara to check if paths are feasible before exploring them.

–dpor

Performs dynamic partial order reduction as described in the following Arxiv article:

–show-ssa

Print the verification conditions (in SSA) that Impara is generating.

–dot graph.dot

Tells Impara to produce a graph representation of the abstract reachability tree and store it in file graph.dot.

