# Golden base-four research certificates

Research continuation of PR #5405 at a02a13c3e358c262355013e712d42dfe5e0dae6d.
The mathematical derivation is appended to the existing problem document
`Problems/golden-ratio-base4-dfao-minimality.md`.

The source inputs are the exact 21-state interval table, its first-return
skeleton serialization, the 28 power samples and the finite branch refutation.
The Python and C++ programs are cross-implementation checks by the same authoring
assistant. No independent-author review, Lean kernel verification or LRAT
verification is claimed.

Run `sh reproduce.sh` using Python 3.10+ without optimization and a C++17 compiler
supporting __int128. It rebuilds the machine JSON, global distinguishing witnesses,
and reports, then replays the supplied refutation without a SAT/SMT solver.
Default finite regression is 100,000 integers and 2,000 powers; use
`INTEGERS=1000000 POWERS=5000 sh reproduce.sh` for the original larger ranges.
The exact interval proof checks, rather than a finite regression cutoff, supply
the mathematical induction for all legal inputs.

To regenerate the refutation:

```sh
g++ -O3 -std=c++17 -Wall -Wextra -Werror gap3_exhaust.cpp -o gap3_exhaust
./gap3_exhaust gap3_core_rows.tsv 30 regenerated_gap3_refutation.txt
python check_gap3_proof.py gap3_core_rows.tsv regenerated_gap3_refutation.txt
```

Discovery timeout is UNKNOWN. Only a complete accepted replay is a refutation.
The C++ interval checker is a bounded research checker for the supplied small
coordinates, not a hardened parser for arbitrary adversarial integer inputs.
Python verification uses arbitrary-precision integers and exact rational arithmetic.

Optional common-suffix graph regeneration uses networkx:

```sh
python suffix_graph.py --count 79
python suffix_graph.py --count 200
```

Graph reports, machine JSON, pair witnesses, compiled binaries and local run
reports are reproducible outputs. They are not additional input authorities.
The global-input witnesses apply to all legal integers, not only powers of four.
The inherited published total-state lower bound 15 is not re-certified here.
No power-restricted exact minimality theorem is claimed.
