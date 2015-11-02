Impara is a software model checker for multi-threaded C programs with POSIX and WIN 32 threads.

[SVCOMP 2016: Binary and Sources](https://github.com/bjowac/impara/releases/tag/0.4.5)


Use the SVCOMP binary or build yourself:

* Obtain CBMC (tested with latest SVN version 5927):

svn co http://www.cprover.org/svn/cbmc/trunk cbmc

* Set the path to CBMC in the Impara config file. For this, please modify variable CBMC in file:

impara/trunk/src/config.template

copy the file to impara/trunk/src/config.

* Run make in directory impara/trunk/src
