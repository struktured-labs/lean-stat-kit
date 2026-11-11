#!/bin/bash
# dev helper: compile one module of the kit (headless). Usage: ./devc.sh StatKit/Csv
K=$HOME/scratch/lean-stat-kit
L=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
M=${MATHLIB_ENV:-$HOME/scratch/mathlib-v4.35.0}
MP=$(ls -d $M/.lake/packages/*/.lake/build/lib/lean | tr "\n" ":")
export LEAN_PATH=$K/.out:$MP$($L --print-libdir)
cd $K; mkdir -p .out/$(dirname $1)
$L -o .out/$1.olean $1.lean
