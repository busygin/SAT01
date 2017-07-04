#!/bin/sh

if [ $# -eq 0 ]; then
    echo "Syntax: factor.sh <number>"
    echo "(e.g., try 255)"
    exit 1
fi

./factor2sat01 $1
./sat01 $1.sat01
./factor_out2sol $1.out
cat $1.sol
