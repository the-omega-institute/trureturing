#!/bin/sh
set -eu
cd "$(dirname "$0")"
g++ -O2 -std=c++17 -Wall -Wextra -Werror check21.cpp -o check21
python verify21.py --integers "${INTEGERS:-100000}" --powers "${POWERS:-2000}"
./check21 machine21.tsv > cpp_verification21.json
python verify_skeleton21.py
python check_gap3_proof.py
python test_rejection.py
printf '\nAll requested certificate checks passed. No Lean kernel check was performed.\n'
