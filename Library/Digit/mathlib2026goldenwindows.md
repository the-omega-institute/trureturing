---
bibkey: mathlib2026goldenwindows
authors: Mathlib contributors
year: 2026
title: Zeckendorf representations and golden rotation phases in Mathlib
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Nat/Fib/Zeckendorf.lean
claim: Canonical Fibonacci digits decode to their natural number; the finite signed golden-conjugate sum equals the golden rotation phase, which avoids positive negative-index cuts.
strata_touched:
  - D5/S1/Digit/Infinite/SparseWindowMutualDetermination
license: Apache-2.0
triage: anchor
---

# Canonical Fibonacci digits and circle phases

Mathlib at revision `db584cd6d46c92f209a44c0f1c829460d327499d` supplies
`Nat.isZeckendorfRep_zeckendorf` and `Nat.sum_zeckendorf_fib` in
`Data/Nat/Fib/Zeckendorf.lean`. They express canonicality and exact decoding.
The raw digit conversion and Boolean row used here are repository encodings
of that same representation; their digitwise agreement follows from membership
in the canonical list. The full conjunction in `natural_row_raw_data` is this
standard representation statement expressed in those two encodings.

`NumberTheory/Real/GoldenRatio.lean` supplies
`Real.fib_succ_sub_goldenRatio_mul_fib`: the difference between the next
Fibonacci number and the current one times the golden ratio is the corresponding
power of the conjugate. Writing the reciprocal golden ratio as alpha makes the
conjugate equal to -alpha. For a finite canonical expansion of n, summing this
identity shows that its signed value differs from n times the golden ratio by
an integer. Projection modulo one gives `natural_row_phase`. This is the
standard Fibonacci identity applied to a finite digit sum, rather than an
independent identity for the golden ratio.

The same file supplies `Real.goldenRatio_irrational`.
`Topology/Instances/AddCircle/Defs.lean` supplies `AddCircle.coe_eq_zero_iff`,
which identifies zero circle phase with an integral period. Equality of the
natural phase of n and the cut E(k), defined as the phase of -k times the golden
ratio, would make (n+k) times the golden ratio an integer. For k positive,
n+k is nonzero, contradicting irrationality. This gives
`natural_phase_avoids_cut` with its exact positive-index hypothesis.

These three auxiliary statements are literature-attested applications of the
pinned library. The particular closed-cylinder endpoint alternatives used by
`natural_window_arc` and the sparse observation tuples used by
`missing_cut_witness` and `extra_cut_witness` are repository constructions.
The cited Mathlib statements do not supply those cylinder or sparse-tuple
conclusions.

## Verified locators

- [Zeckendorf representations](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Nat/Fib/Zeckendorf.lean).
- [Golden-ratio identities and irrationality](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/Real/GoldenRatio.lean).
- [Circle quotient and integral periods](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Instances/AddCircle/Defs.lean).
