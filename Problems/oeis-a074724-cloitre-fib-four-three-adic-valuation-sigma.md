---
slug: oeis-a074724-cloitre-fib-four-three-adic-valuation-sigma
bibkey: cloitre2002a074724
doi: null
url: https://oeis.org/A074724
triage: theorem
motivation_gids:
  - D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma
---

# The Marcus and Bala formulas for the power of three in F(4n)

## Problem

OEIS A074724, NAME (`%N`, verbatim):

> Highest power of 3 dividing F(4n) where F(k) is the k-th Fibonacci number.

Marcus's FORMULA (`%F`, verbatim):

> a(n) = 3^A051064(n) (conjectured). - _Michel Marcus_, May 17 2022

Bala's FORMULA (`%F`, verbatim):

> Conjecture: a(n) = (sigma(3*n) - sigma(n))/(sigma(3*n) - 3*sigma(n)), where sigma(n) = A000203(n). Equivalently, a(n) = A088838(n) - A074724(n). - _Peter Bala_, Jun 10 2022

The AUTHOR line (`%A`, verbatim) is:

> _Benoit Cloitre_, Sep 04 2002

With `a n = 3 ^ padicValNat 3 (Nat.fib (4 * n))`, the exact claim is
`forall n : Nat, 0 < n ->
(a n = 3 ^ (padicValNat 3 n + 1) and
a n * (sigma 1 (3 * n) - 3 * sigma 1 n) = sigma 1 (3 * n) - sigma 1 n)`.
Here A051064(n) is `v_3(3n) = v_3(n)+1`. Bala's denominator is multiplied out
in natural numbers; its positivity is proved within the proof. The separate
"Equivalently" remark involving A088838 is not part of this claim. The
positive-index guard excludes the totalized Lean value at zero.

## Motivation

The two formulas connect Fibonacci divisibility with a divisor-sum identity
for every positive natural index. The independent question is the pair of
2022 conjecture lines, registered in issue #7976 on 2026-09-15T00:33:26Z before
the probe began at 2026-09-15T00:34:10Z.

## Gap

Readings of 2026-09-15. OEIS still marks both
FORMULA lines as conjectured and supplies no settlement line. Sela Fried
(2025, OEIS `a006519.pdf`) proved the `p = 2` analogue on A006519, not this
entry. Lengyel (1995) already gave the general p-adic valuation of Fibonacci
numbers; the valuation clause has that prior literature even though OEIS
retains the conjecture label. The module proves that clause directly.

The arXiv API returned HTTP 429 at query time and was not searched. OpenAlex
returned 0 results; MathOverflow returned 0; GitHub code search found only
OEIS mirrors; formal-conjectures returned 0. Repository searches for A074724
and A051064 returned 0 hits, and no 3-adic Fibonacci valuation declaration was
found in D5 or pinned Mathlib: `padicValNat` and `fib` did not co-occur in a
mathematical declaration. These scoped readings do not establish exhaustive
historical openness or priority.

## Route

1. Use the Fibonacci gcd identity and the divisors of 12 to prove, for every
   positive `k`, that `9` divides `F(k)` exactly when `12` divides `k`.
2. Derive `F(3(4m)) = F(4m)(5F(4m)^2+3)` from the addition identities and
   Cassini's identity. The second factor has 3-adic valuation one.
3. Write `n = 3^e m` with `m > 0` and `3` not dividing `m`. The rank criterion
   gives `v_3(F(4m)) = 1`; induction on `e` gives `v_3(F(4n)) = e+1`.
4. Apply multiplicativity of the divisor sum to the coprime factors and the
   geometric sums for powers of three. The denominator becomes `sigma(m)>0`
   and the numerator becomes `3^(e+1)*sigma(m)`, yielding Bala's identity.

## Falsifier

A positive natural index `n` violating either the valuation equality or the
multiplied divisor-sum equality would contradict the claim. A nonpositive
denominator at a positive index would invalidate the stated correspondence
with Bala's quotient. Bounded numerical agreement alone does not prove the
unbounded statement.

## Evidence

- Module: `D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.lean`; theorem `result`.
- Final single-file Lean profile (after inlining the rank-12 helper): exit 0;
  wall time 12.3 seconds and type checking 65.9 milliseconds, with Lean
  v4.33.0 on macOS 26.6.2 arm64 and a warm cache, measured while other
  seats shared the machine.
- Header check: exit 0; generality G, 312 lines and 45 Lean files in the bucket.
- The single-file axiom and dependency audit exits 0. Both `a` and `result`
  have exactly `[propext, Classical.choice, Quot.sound]`; the proof uses
  `result -> fib_four_valuation`; the rank-12 criterion `9 | F(k) <-> 12 | k`
  is a proof step (`have`) inside the valuation lemma, not a declaration.
- Deleting each of the five direct imports alone via process substitution
  makes Lean exit 1: `Mathlib.Data.Int.Fib.Lemmas`,
  `Mathlib.NumberTheory.Padics.PadicVal.Basic`,
  `Mathlib.NumberTheory.ArithmeticFunction.Misc`,
  `Mathlib.Tactic.NormNum.NatFib`, and `Mathlib.Tactic.NormNum.Prime`.
- Maximum resident set size was not measured (`/usr/bin/time -l` exits 1
  under the sandbox). Wall time was measured around the bare Lean command.
  The final module compiles with zero warnings.
- Numerical checks for `1 <= n <= 400` and `1 <= n <= 2000` found zero
  exceptions; these bounded scans support fault detection only.
- Whole-tree `make lean-report` exit 0 (`LEAN_REPORT_DELTA mode=delta
  changed=0 added=4 removed=1 recheck=4`) and whole-tree `make lean` exit 0
  (`Build completed successfully (13370 jobs)`) on the landed lane tree
  (parent `344be0c4c7`); header check exit 0; Scribe
  `FormulaCorpusInventoryTests` exit 0.

## Triage

`theorem`; resolution `proved` for the two displayed formulas at every
positive natural index.

## ASSUMED-UNVERIFIED

The arXiv search was not performed (HTTP 429 at query time). Historical
openness outside the stated search surfaces (OEIS text, OpenAlex,
MathOverflow, GitHub code search, formal-conjectures, repository prior art)
is unverified, and no exhaustive novelty or priority claim is made. The
bounded numerical scans do not establish the universal statement.
