#!/bin/bash

CURRENT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SOLVER_DIR=$SMT_SOLVERS_BIN_DIR/z3
cd $SOLVER_DIR
d=`ls |grep -v tar.gz`
cd $d/bin
SOLVER_BIN_DIR=`pwd`
$SOLVER_BIN_DIR/z3 -smt2 -in
