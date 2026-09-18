---
slug: oeis-a319197-lang-fib-dyadic-index-divisibility
bibkey: lang2018a319197
doi: null
url: https://oeis.org/A319197
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LangFibDyadicIndexDivisibility
---

# Dyadic divisibility at Lang's Fibonacci indices

## Problem

OEIS A319197, NAME (`%N`, verbatim):

> All entries from a(3) to a(n) appear in addition to 2^n as factors in the conjectured factorization of Fibonacci(2^(n-2)*3*m) for n >= 3 and all m >= 0.

The first COMMENT sentence (`%C`, verbatim), which is the settled clause:

> It appears that Fibonacci(2^(n-2)*3*m)/(2^n) is a nonnegative integer for n >= 3 and all m >= 0.

AUTHOR (`%A`, verbatim):

> _Wolfdieter Lang_, Oct 09 2018

The exact Lean statement is
`theorem result (n m : ℕ) (hn : 3 ≤ n) : 2 ^ n ∣ Nat.fib (2 ^ (n - 2) * 3 * m)`.
The natural-number domain includes `m=0`; `n-2` is truncated subtraction,
which agrees with ordinary subtraction under `3 <= n`. The positive divisor
`2^n` makes natural divisibility equivalent to the quoted
nonnegative-integral quotient assertion, not a claim about truncated division.

Only that first COMMENT sentence is settled. The product
`A(n) = Product_{j=3..n} a(j)`, the `I(n; m)` factorization conjecture, the
specific factors from A049660 and A253368, and the rest of the entry are not
claimed. The theorem does not assert an exact 2-adic valuation.

## Motivation

The stated power of two is a uniform divisor for every natural multiplier
and every dyadic level starting at `n=3`. A direct induction establishes this
unbounded divisibility assertion independently of the remaining proposed
factors in A319197.

## Gap

Readings of 2026-09-15. OEIS
still opens the comment with "It appears" and carries no proof line and no
Lengyel reference. OpenAlex returned zero results for `A319197`,
MathOverflow returned zero, and formal-conjectures returned zero. GitHub
code search returned only unrelated non-mathematical hits. The arXiv API
returned HTTP 503 at query time: arXiv was not searched.

The repository prior-art search at
`origin/dev = d1c9a61ae9` found zero `A319197` hits. Hits for
`2-adic valuation` concerned only `IsraelLaguerreFourParity`, whose object is
Laguerre numbers. No 2-adic Fibonacci divisibility theorem was found in D5
or pinned Mathlib: `padicValNat` and `fib` never co-occurred in that search.
The A074724 lane #7976 concerns the 3-adic analogue in an independent module.

No direct theorem for the full dyadic divisibility statement was found in
the frozen-project and pinned-Mathlib search scope; a direct `exact?`
binding attempt failed on the unbounded power-divisibility
obligation. This is `not-found-in-searched-scope`, not an exhaustive absence
claim. Pre-registration issue #7988 was created on 2026-09-15 before the
probe started.

Lengyel (1995), "The order of the Fibonacci and Lucas numbers", Fibonacci
Quarterly 33, gives the general exact 2-adic valuation of Fibonacci numbers.
That prior literature is acknowledged in `lang2018a319197`; no mathematical
priority or claim of a previously unknown consequence of that valuation is
made here.

## Route

1. Apply `Nat.le_induction` to the level `n`, starting at `n=3` with arbitrary
   natural `m`. Compute `Nat.fib 6 = 8` and use `Nat.fib_dvd` to transport
   divisibility from index `6` to `6*m`.
2. At the successor step, write `k = 2^(n-2)*3*m`. The index for `n+1` is
   `2*k`, and `Nat.fib_two_mul` gives
   `Nat.fib (2*k) = Nat.fib k * (2*Nat.fib (k+1) - Nat.fib k)`.
3. The induction hypothesis gives `2^n` dividing `Nat.fib k`, and hence `2`
   dividing it. Both terms of the cofactor are even, so `Nat.dvd_sub` gives
   an even cofactor. Apply `mul_dvd_mul` and normalize `2^(n+1)` to finish.

The sole public theorem has `proof_shape: content` and
`admission_basis: escape-witness`, using the public-conclusion form of the
witness: the induction constructs the unbounded dyadic divisibility
invariant on the live proof path. There are no separately authored public
or private helpers and no direct frozen-project dependencies.
`utility: none` describes an unbounded arithmetic theorem; the internal
base computation is not a separate finite-instance result.

## Falsifier

A natural pair `n >= 3`, `m >= 0` with
`Nat.fib (2^(n-2)*3*m) % (2^n) != 0` would refute the stated divisibility.
The case `m=0` is included: its Fibonacci value is zero and is divisible by
`2^n`.

## Evidence

- Lean module: `D5/S1/Recurrence/LangFibDyadicIndexDivisibility.lean`.
- `lake env lean` on that module: exit 0. The exact theorem statement and
  proof were copied from the verified probe.
- `tools/scripts/agent/header-check.sh` on that module: exit 0; 35 lines,
  31 Lean files in the immediate directory, `generality: G` compliant.
- The scratch `#print axioms` audit: exit 0, with exactly
  `[propext, Classical.choice, Quot.sound]` for
  `D5.S1.Recurrence.LangFibDyadicIndexDivisibility.result`.
- The sole direct import is `Mathlib.Data.Nat.Fib.Basic`. Deleting it alone
  through process substitution and recompiling exits 1, reporting unknown
  Fibonacci notation/constants and an unknown tactic. No separate tactic
  import is needed because the Fibonacci module supplies the required
  tactics transitively.
- `lake env lean -Dprofiler=true -Dtrace.profiler.threshold=1000` on the
  module: exit 0; `/usr/bin/time -p` wall time 1.98 seconds, Lean type
  checking 13.9 milliseconds. This is a warm-cache single-file measurement
  in the assigned macOS worktree.
- Numerical checks: zero exceptions for `3 <= n <= 9`, `m < 60` and for
  `3 <= n <= 12`, `m <= 100` (1010 pairs). These finite scans support fault
  detection only; the Lean induction carries the unbounded statement.
- Whole-tree `make lean-report` exit 0 (`LEAN_REPORT_DELTA mode=delta
  changed=0 added=2 removed=1 recheck=2`) and whole-tree `make lean` exit 0
  (`Build completed successfully (13371 jobs)`) on the landed lane tree
  (parent `198f814cd0`); header check exit 0; Scribe
  `FormulaCorpusInventoryTests` exit 0.

## Triage

`theorem`; resolution `proved` for the first quoted COMMENT sentence, with
the explicit scope wall above.

## ASSUMED-UNVERIFIED

The arXiv search was not performed (HTTP 503 at query time). Historical
openness outside the stated search surfaces (OEIS text, OpenAlex,
MathOverflow, GitHub code search, formal-conjectures, repository prior art)
is unverified, and no exhaustive literature or priority claim is made. The
bounded numerical scans do not establish the universal statement.
