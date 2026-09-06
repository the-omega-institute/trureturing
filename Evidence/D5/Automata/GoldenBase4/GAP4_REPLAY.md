# Complete gap4 evidence reconstruction

The earlier checked-in `gap4_power_rows.tsv` and three `.proof.xz` files did not
match the checked originals. They have been removed from this branch rather
than retained as purported certificates. Git history preserves those failed
uploads. The complete original evidence is now losslessly reconstructible from
the retained deterministic producer, arithmetic sample generator and expected
SHA-256 hashes. No network or third-party solver is required.

Run from any checkout:

```sh
sh Evidence/D5/Automata/GoldenBase4/reproduce_gap4.sh /tmp/phi4-gap4-replay
```

The argument is an output directory, not the repository root. This generates
144 exact rows from powers with indices 0 through 249, compiles the retained
producer and separate checker, recreates the three original proof streams,
compares each complete stream with its original hash, replays all 48 output
cases, and runs eight corruption tests. SHA checks attest byte integrity only;
the separate replay recomputes the arithmetic and validates every proof step.
An incomplete producer run stops reproduction and cannot be accepted as UNSAT.

The complete source inputs are `gap4_produce.cpp`, `rebuild_gap4.py`,
`check_gap4_certificate.cpp`, and `test_gap4_rejection.py`. Generated proof trees
and TSV data go to the supplied output directory; no damaged binary fragments
are needed. The generated proof format remains `gap4-proof-v1`.

The verified mathematical/computational result excludes at most four
previous-one states, with no bound on the previous-zero side. It supports
`s >= 5` after the stated signature reduction. It is not a new total-state
lower bound. The generated external proof is not yet evaluated by the Lean
kernel; the formal model-normalization and concrete certificate transport
obligations remain separate.
