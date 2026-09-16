---
slug: oeis-a347293-schulte-shifted-product-gcd-row-sum-convolution
bibkey: schulte2022a347293
doi: null
url: https://oeis.org/A347293
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution
---

# Schulte's shifted-product gcd row-sum convolution

## Problem

OEIS A347293, NAME (`%N`, verbatim):

> Triangle read by rows: T(n, k) = Sum_{i=1..n} gcd(1 + (i-1) * (k-1),n) for 1 <= k <= n.

FORMULA (`%F`, verbatim):

> Conjecture: Row sums equal Dirichlet convolution of A000290 and A127473.

A000290 is the square function and A127473 is the square of Euler's totient.
Thus the full-quantifier statement is that for every positive natural `n`,

`Sum_{x=0}^{n-1} Sum_{y=0}^{n-1} gcd(1+x*y,n)
 = Sum_{d|n} d^2 * phi(n/d)^2`.

The left side is the triangle row sum after the index changes `x=i-1` and
`y=k-1`. The divisor sum is the pointwise definition of the stated
Dirichlet convolution.

## Motivation

The problem is a named 2022 OEIS conjecture giving a closed divisor formula
for a two-dimensional gcd sum. It asks for one identity at every positive
index, with no finite bound on `n`.

## Gap

The OEIS Formula line remained labelled `Conjecture` on 2026-09-16 and gave
no proof. Searches for `A347293`, the shifted-product gcd sum, and the
totient-square conclusion found no proof in the checked OpenAlex, Math.SE,
arXiv, GitHub formal-conjectures, pinned Mathlib, or repository surfaces.
These scoped negative readings do not establish exhaustive historical
openness or priority.

## Route

For a positive divisor `d` of `n`, reduction modulo `d` sends the pairs
`(x,y)` with `d | 1+xy` to pairs in `ZMod d`. The first coordinate must be a
unit, and the second is its unique negative inverse. This gives exactly
`phi(d)` residue pairs. Each coordinate residue has `n/d` representatives in
`Fin n`, giving

`Nat.card {p : Fin n x Fin n // d | 1+p.1*p.2}
 = phi(d) * (n/d)^2`.

Expanding `gcd(1+xy,n)` as a sum of totients over its positive divisors and
reordering the finite sums yields
`Sum_{d|n} phi(d)^2 * (n/d)^2`. The divisor involution `d |-> n/d` converts
this to `Sum_{d|n} d^2 * phi(n/d)^2`.

## Falsifier

Any positive natural `n` for which the double gcd sum differs from the
divisor convolution would contradict the theorem. A failure of the modular
pair count for any positive `d | n` would contradict its load-bearing
counting lemma.

## Evidence

- Lean module:
  `D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.lean`.
- Public declarations: `rowSum` and `result`.
- The load-bearing count is `card_window_solutions`.
- The probe self-reported zero exceptions for `1 <= n < 80`. Independently,
  the implementation measured `n=60` and obtained `12792` on both sides.
  These finite readings support fault detection only.

## Triage

`theorem`. The formal result proves the convolution identity for every
positive natural `n`.

## ASSUMED-UNVERIFIED

Historical openness beyond the checked OEIS, OpenAlex, Math.SE, arXiv,
GitHub, pinned Mathlib, and repository surfaces is unverified. No exhaustive
literature or priority claim is made. The bounded computation does not prove
the universal identity.
