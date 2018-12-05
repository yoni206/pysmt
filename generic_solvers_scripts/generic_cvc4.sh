#!/bin/bash
file=$1
CURRENT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SOLVER_DIR=$CVC4_DIR
cd $SOLVER_DIR
SOLVER_BIN_DIR=`pwd`
cd $CURRENT_DIR
#$SOLVER_BIN_DIR/cvc4 --lang=smt2 --tlimit 3000 --produce-model-cores $file
$SOLVER_BIN_DIR/cvc4 --lang=smt2 --tlimit 3000 $file
