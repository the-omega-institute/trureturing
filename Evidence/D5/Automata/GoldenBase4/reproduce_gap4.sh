#!/bin/sh
# Replay the retained certificate. No search or SAT/SMT solver is invoked.
set -eu
root=${1:-.}
evidence="$root/Evidence/D5/Automata/GoldenBase4"
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT HUP INT TERM
${CXX:-g++} -std=c++17 -O2 "$evidence/check_gap4_certificate.cpp" -o "$build/check_gap4"
for stem in gap4_0_16 gap4_16_32 gap4_32_48; do xz -dc "$evidence/$stem.proof.xz" > "$build/$stem.proof"; done
"$build/check_gap4" "$evidence/gap4_power_rows.tsv" \
  "$build/gap4_0_16.proof" \
  "$build/gap4_16_32.proof" \
  "$build/gap4_32_48.proof"
