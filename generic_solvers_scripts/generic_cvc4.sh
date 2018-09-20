#!/bin/bash

CURRENT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SOLVER_DIR=$SMT_SOLVERS_BIN_DIR/cvc4
cd $SOLVER_DIR
d=`ls |grep -v tar.gz`
cd $d/builds/bin
SOLVER_BIN_DIR=`pwd`
$SOLVER_BIN_DIR/cvc4 --lang="smt2" -
