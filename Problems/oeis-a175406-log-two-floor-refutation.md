---
slug: oeis-a175406-log-two-floor-refutation
bibkey: greathouse2012a175406
doi: null
url: https://oeis.org/A175406
triage: theorem
motivation_gids:
  - D5/S0/Certificates/GreathouseLogTwoFloorRefutation
---

# Refutation of the A175406 floor formula conjecture

## Problem

OEIS A175406 %N (verbatim):

> The greatest integer k such that (1+1/n)^k <= 2

OEIS A175406 %C (verbatim):

> The sequence of first differences consists of zeros and ones, with no two consecutive zeros and no more than three consecutive ones.

OEIS A175406 %F (verbatim):

> a(n) = n log 2 + O(1). Conjecture: a(n) = floor((n + 1/2) log 2). - _Charles R Greathouse IV_, Apr 03 2012

OEIS A175406 %A (verbatim):

> _Zak Seidov_, May 01 2010

The literal claim formalized here is
`∀ n : ℕ, 1 ≤ n → a n = ⌊((n : ℝ) + 1 / 2) * Real.log 2⌋₊`.
The definition of `a` uses the literal natural supremum
`sSup {k : ℕ | (1 + 1 / (n : ℝ)) ^ k ≤ 2}`; in the natural conditionally
complete order, an unbounded set has `sSup = 0`. The result refutes this
universal claim at one explicit positive index.

## Motivation

The entry presents a universal floor formula for the greatest admissible
exponent. A kernel-checked explicit counterexample resolves the literal
conjecture while leaving the asymptotic statement and the difference-pattern
observation as separate questions.

## Gap

The search record on preregistration issue #7587 and the probe report is dated
September 13, 2026. The OEIS history has 25 revisions: revision 3 introduced
the conjecture, and revision 25 (2026-03-09) still marks it as a conjecture.
The bounded search found 0 arXiv results, 0 results for OEIS Open arXiv:2608.11941
and LeanOpenProblems, 0 in formal-conjectures, 0 on MathOverflow, and 0 across
DataCite / OpenAIRE. OpenAlex returned HTTP 429 and is
`ASSUMED-UNVERIFIED`. Heuristically equidistribution suggests that the floor
conjecture must fail somewhere, and no explicit counterexample was found in the
surfaces listed above (bounded search; OpenAlex unverified) before this witness;
no priority claim is made.

## Route

The proof uses one certified estimate chain. (i) `Real.hasSum_log_one_add_inv`
at `a = 1` gives the 36-term lower sum `S36` and the geometric upper tail
`S36 + 3⁻⁷²` for `log 2`. (ii) At `n₀ = 1121626023352383`, the same series
gives a lower bound from its first two positive terms for
`log(1 + 1/n₀)`, while `Real.log_le_sub_one_of_pos` gives the upper bound
`log(1 + x) ≤ x`. (iii) Exact rational normalization yields
`⌊(n₀ + 1/2) log 2⌋₊ = M` with `M = 777451915729368`, and proves
`(1 + 1/n₀)^M > 2` while `(1 + 1/n₀)^(M−1) ≤ 2`. Hence the defining supremum
is `M − 1`, not `M`.

The search seat found the witness through the continued fraction of `log(2)/2`;
the convergent index was 36 and `q = 2n₀ + 1`. This is context only.

## Falsifier

A proof of the literal universal claim would contradict the kernel theorem
`D5/S0/Certificates/GreathouseLogTwoFloorRefutation.result`, because its
specialized value at `n₀` would identify `a(n₀)` with `M` even though the
certified defining supremum is `M − 1`.

## Evidence

- Lean module: `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.lean`.
- Main theorem: `result : ¬ claim`, with std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- Step 0 import deletion exits were: `Mathlib.Algebra.Order.Floor.Semiring=0`,
  `Mathlib.Analysis.SpecialFunctions.Log.Deriv=1`,
  `Mathlib.Analysis.SpecialFunctions.Pow.Real=1`, and
  `Mathlib.Tactic.NormNum=0`. The retained anchors are the two imports whose
  deletion breaks the build.
- The Step 0 profiler on the stamped hot tree reported 7.14 seconds wall
  time, 31.8 ms cumulative type checking, and 2,400,796,672 bytes maximum RSS.
- An independent 80-digit decimal recomputation found 0 mismatches for
  `1 ≤ n ≤ 20000`, and recorded
  `(n₀ + 1/2)·log 2 − M = +1.476015…×10⁻¹⁷` and
  `M·log(1 + 1/n₀) − log 2 = +3.275470…×10⁻³²`.
- The probe's Decimal(100) reading agrees and gives
  `(M − 1)·log(1 + 1/n₀) − log 2 = −8.916×10⁻¹⁶`.

## Triage

`theorem`. The explicit kernel-checked witness refutes the literal universal
floor formula and does not propose a corrected formula.

## ASSUMED-UNVERIFIED

OpenAlex returned HTTP 429. The literature search is bounded, and no claim of
exhaustive publication coverage is made. **Minimality (not claimed):** the
search seat's Legendre-reduction argument that `n₀` is the least counterexample
is unverified and is not formalized.
