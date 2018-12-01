#!/bin/bash
file=$1
CURRENT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SOLVER_DIR=$YICES_DIR
cd $SOLVER_DIR
SOLVER_BIN_DIR=`pwd`
cd $CURRENT_DIR
$SOLVER_BIN_DIR/yices-smt2 $file