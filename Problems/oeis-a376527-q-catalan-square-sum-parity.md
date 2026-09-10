---
slug: oeis-a376527-q-catalan-square-sum-parity
bibkey: hanna2024a376527
doi: null
url: https://oeis.org/A376527
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalan_unique
  - D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.binary_catalan
---

# Parity of q-Catalan row square sums

## Problem

OEIS A376527 defines

> a(n) = Sum_{k=0..n*(n-1)/2} A227543(n,k)^2.

Paul D. Hanna's comment of October 11, 2024 states, verbatim:

> Conjecture: a(n) is odd iff n = 2^k - 1 for some k >= 0.

Here A227543 is the Carlitz-Riordan q-Catalan triangle defined by
`A(x,q) = 1 + x*A(q*x,q)*A(x,q)`.

## Motivation

The assertion covers every natural row index, including zero. For the first
fifteen listed values, the odd indices are `0, 1, 3, 7`; this is supporting
evidence rather than a proof of the universal statement.

## Gap

Repository searches found no A376527 declaration. Pinned Mathlib contains no
Carlitz-Riordan q-Catalan development. The repository does contain the shifted
Catalan equation, its uniqueness theorem, and its binary support theorem, but
no typed bridge from q-Catalan rows to that series.

## Route

Let `R_n(q)` be the nth row polynomial. Coefficient extraction from the
defining bivariate equation gives `R_0=1` and
`R_(n+1)=Sum_{i+j=n} q^i R_i R_j`. This recurrence is used directly as the
row-polynomial definition.

Evaluation at `q=1` gives the Catalan convolution for the row sums. After a
one-place shift, their generating series has zero constant coefficient and
satisfies `F=X+F^2`. The established uniqueness theorem identifies it with the
shifted Catalan series.

The degree of `R_n` is at most `n*(n-1)/2`, so evaluation at one is exactly the
finite sum across the A227543 row. Modulo two, `u^2=u` term by term. Thus the
square sum reduces to the row sum, and the established binary Catalan theorem
places coefficient one precisely at indices `2^k`. Accounting for the series
shift gives `n=2^k-1`.

## Falsifier

A natural row index whose square sum has oddness different from membership in
`{2^k-1 : k >= 0}` would contradict the theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.lean`.
- Resolution anchor: `hanna_conjecture`.
- Row recurrence: `qCatalanRow_succ`.
- Catalan bridge: `rowSum_eq_catalan`.
- Parity companion: `squareSum_mod_two_eq_catalan`.
- Directed dependencies: `rowSum_eq_catalan` to `catalan_unique`, and
  `hanna_conjecture` to `binary_catalan` through the parity companion.

The exact final statement is:

```lean
theorem hanna_conjecture (n : ℕ) :
    Odd (squareSum n) ↔ ∃ k : ℕ, n = 2 ^ k - 1
```

## Triage

`theorem`. The formal proof closes the universal parity assertion recorded by
OEIS.

## ASSUMED-UNVERIFIED

The source wording, attribution, date, and numerical check were supplied by
the implementation brief. Source-to-Lean identification and publication
priority are not kernel-checked facts.
