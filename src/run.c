#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include "hvm.c"


// Monadic IO Evaluator
// ---------------------

// Runs an IO computation.
void do_run_io(Net* net, Book* book, Port port) {
  exit(-1);
}
