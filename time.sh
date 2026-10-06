#!/usr/bin/env bash

syntax=implicit
tests=("nat" "bin" "queue" "stack" "tree" "avl_tree" "mapreduce" "ring_leader" "auction")

mkdir -p times

export OCAMLRUNPARAM="s=1000000000,o=1000000"
for t in "${tests[@]}"; do
    echo "$t"
    rm -f times/$t.times
    for i in {1..10}; do
        ./_build/default/bin/fracst.exe -v 2 -s $syntax tests/$syntax/$t.frac >> times/$t.times
    done
    awk '{sum+=$1; count++} END {if (count > 0) print sum/count}' times/$t.times
done

