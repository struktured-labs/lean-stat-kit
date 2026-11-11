#!/bin/bash
# dev helper: compile one module of the kit (headless) into .out/. Usage: ./devc.sh StatKit/Csv
K=$(cd "$(dirname "$0")" && pwd)
L=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
M=${MATHLIB_ENV:-$K/mathlib-env}
MP=$(ls -d $M/.lake/packages/*/.lake/build/lib/lean | tr "\n" ":")
export LEAN_PATH=$K/.out:$MP$($L --print-libdir)
cd $K; mkdir -p .out/$(dirname $1)
$L -o .out/$1.olean $1.lean
