---
slug: pisano-order-range-refutation
bibkey: benfieldlippard2025pisanozeros
doi: null
url: https://arxiv.org/abs/2407.20048v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/PisanoOrderRangeRefutation.result
---

# The Order of a Pisano Period Is Not Confined to Two

## Problem

Benfield and Lippard, *Connecting Zeros in Pisano Periods to Prime Factors of K-Fibonacci
Numbers*, arXiv:2407.20048v2, 30 January 2025, close with Conjecture 5.3 on the range of the
order as the parameters of a two-term recurrence vary. Clause (v) reads, from the LaTeX source
`fiborder.tex`:

> `\item $\{0,1,2\}$ if $b \neq \pm1$ and $|a|-|b| = 1$,`

Section 4 defines the objects: `F_0 = 0`, `F_1 = 1`, `F_n = a F_{n-1} + b F_{n-2}`. Section 1
defines the order: "The number of zeros in a Pisano period is the order of `m`, denoted
`omega(m)`." Section 5 fixes the degenerate convention: "define the order to be zero if the
sequence is eventually periodic modulo `m` and this period contains no multiples of `m`."

Written out, the assertion is that for all integers `a`, `b` and all `m > 1`, if `b ≠ ±1` and
`|a| - |b| = 1`, then `omega_(a,b)(m) ∈ {0,1,2}`.

## Motivation

The frozen theorem `D5/S3/Arith/PisanoOrderRangeRefutation.result` refutes it.

## Gap

Issue 9448 records the screen carried out before the probe. The conjecture does not appear in
the repository's screening records, under `Problems/`, `D5/` or `Library/`; no follow-up on
arXiv cites it. Citation indices were not exhaustively reachable, so this is a bounded negative
finding.

## Route

The repository already carries the machinery, so the settlement reuses it rather than rebuilding
it. Its Lucas convention is `x_{n+1} = p x_n - q x_{n-1}`, so the paper's `(a,b)` is
`(p,q) = (a,-b)`. `D5/S1/Recurrence/LucasEvenDescent` supplies the sequence, the entry point and
the theorem that the zero indices are exactly the multiples of the entry point;
`D5/S1/Recurrence/LucasCompanion` supplies the period as the order of the companion matrix.
Because the zeros are exactly those multiples and a period ends on a zero, the number of zeros
in one period is the period divided by the entry point.

Take `(a,b) = (3,2)` and `m = 13`, so `p = 3` and `q = -2`, a unit modulo 13 with inverse 6. The
terms are `0, 1, 3, 11, 0, 9, 1, 8, 0, 3, 9, 7`, and the pair of consecutive terms then returns
to `(0,1)`, so the period is 12. The entry point is 4: the fourth term is `3 · 11 + 2 · 3 = 39`,
a multiple of 13, while the first three are 1, 3 and 11. The order is `12 / 4 = 3`, outside
`{0,1,2}`, while `b = 2` is not `±1` and `|3| - |2| = 1`.

## Falsifier

A different value for any of the first thirteen terms modulo 13, a different entry point, or a
period other than 12 would invalidate the witness. The term at index 12 is `3 · 7 + 2 · 9 = 39`
and the term at index 13 is `3 · 0 + 2 · 7 = 14 ≡ 1`, which is what closes the period at 12.

## Evidence

The failure is not isolated and its cause is structural. Finiteness of the order in this region
comes from `x^2 - a x - b` having `±1` among its roots: `b = a+1` gives roots `a+1` and `-1`,
`b = 1-a` gives roots `1` and `-a`, and in either case the sequence has a closed form whose
vanishing is governed by a single multiplicative order, so a period carries at most two zeros.
In absolute values that family is `|a| - |b| = 1` when `b < 0` and `|b| - |a| = 1` when `b > 0`.
Clause (v) keeps only the first shape and so admits the pairs `(3,2), (4,3), (5,4), …`, whose
characteristic polynomials have irrational roots — the discriminant at `(3,2)` is 17.

Measured, over `2 ≤ m ≤ 2000` unless stated otherwise:

| family | observed range of the order |
| --- | --- |
| `(3,4)`, `m ≤ 20000` | exactly `{0,1,2}` |
| `b = a+1`, `a = 2..12` | exactly `{0,1,2}` for every `a` |
| `b = 1-a`, `a = 3..11` | contained in `{0,1,2}` for every `a` |
| `b = a-1`, `a = 3..13` | 179 to 229 distinct values |

The first row is the example the paper itself reports having checked; it satisfies
`|b| - |a| = 1` and does not satisfy the condition as printed. The computation was checked
against published facts before being trusted: for the ordinary Fibonacci sequence it returns
exactly `{1,2,4}` over all `m ≤ 4000`, the classical theorem the paper's abstract quotes; it
returns a period of 20 with four zeros at `m = 5`, matching the worked example in Section 4; and
a period of 60 at `m = 10`, Lagrange's 1877 reading quoted in Section 1.

Smaller witnesses with the same shape: `(a,b) = (7,6)` at `m = 5`, period 12, and `(4,3)` at
`m = 5`, period 24.

## Triage

`theorem`; Tier 1 named external conjecture in the closing section of a preprint, preregistered
in issue 9448 before the probe. The admission basis is `open-problem-resolution`; the
conservative classification is `proof_shape: bind-only` with `escape_witness: none`, since the
settlement rests on instantiating frozen prerequisites at a concrete witness. The computational
use is a `certified-instance` with a typed `refutes` edge from `result` to `claim`.

## ASSUMED-UNVERIFIED

The formal claim is the printed clause restricted to moduli where `b` is invertible, that is, to
the case where the sequence is periodic from the start. The restriction weakens the claim, so
refuting it refutes the clause as published; no separate treatment of the degenerate moduli is
offered here.

This settlement refutes clause (v) as published. It does not prove the corrected clause: the
statement that the order stays in `{0,1,2}` whenever `±1` is a root of the characteristic
polynomial is supported here only by the measured ranges above, not by a proof.

The literature screen is bounded: the preprint was read in full and no follow-up citing
Conjecture 5.3 was reachable; citation-index result pages were not exhaustively reachable, so no
worldwide priority claim is made.
