---
slug: oeis-a396843-compositional-square-all-odd-coefficients
bibkey: hanna2026a396843
doi: null
url: https://oeis.org/A396843
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalan_unique
---

# OEIS A396843: all coefficients are odd

## Problem

OEIS A396843 defines `A(x) = Sum_{n>=1} a(n)*x^n` by

> G.f. A(x) satisfies A( x*A(x) - 3*x*A(x)^2 ) = x^2.

Paul D. Hanna's comment of July 1, 2026 states, verbatim:

> Conjecture: all terms are odd.

## Motivation

The listed 23 coefficients are odd, but a finite computation does not prove
the assertion for every positive index.

The existing `catalan_unique` theorem is a same-domain precedent for proving
formal-series identities by successive coefficient determination. The proof
below establishes the needed uniqueness directly and does not invoke that
theorem or a Catalan formula.

## Gap

Repository searches found no A396843 declaration. Pinned Mathlib provides
formal power-series substitution and coefficient lemmas, but no theorem that
directly solves this characteristic-two composition equation.

## Route

Reduce the defining equation modulo two. Write `F` for the reduced series and
`H=x(F+F^2)`. The equation becomes `F(H)=x^2`. Its degree-two coefficient
gives `coeff(1,F)^2=1`, hence `coeff(1,F)=1` in characteristic two.

Suppose two solutions agree below degree `d`. Their inner series agree below
degree `d+1`, and the difference of their degree-`d+1` coefficients is the
difference of the degree-`d` coefficients of the original series. Since each
inner series is divisible by `x^2`, powers from the second onward gain two
further degrees. Comparing degree `d+1` in the two compositions therefore
determines coefficient `d` uniquely. Induction proves uniqueness.

The geometric series `S=x/(1+x)=x+x^2+x^3+...` is a solution. Indeed,
`x(S+S^2)=x^2/(1+x)^2` and substitution gives `S(x(S+S^2))=x^2`.
Uniqueness yields `F=S`, so every positive-degree coefficient reduces to one
modulo two and every corresponding integer coefficient is odd.

## Falsifier

An integer formal power series with zero constant coefficient satisfying the
stated equation and having an even positive-index coefficient would contradict
the theorem.

## Evidence

- Lean module:
  `D5/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients.lean`.
- Resolution declaration: `hanna_conjecture`.
- The proof imports only Mathlib formal power-series and finite-field results.

The exact statement is:

```lean
theorem hanna_conjecture (A : PowerSeries Z) (h0 : constantCoeff A = 0)
    (hEq : A.subst (X * A - 3 * X * A ^ 2) = X ^ 2) :
    forall n, 1 <= n -> Odd (coeff n A)
```

## Triage

`theorem`. The formal proof establishes the universal parity assertion from
the defining equation alone.

## ASSUMED-UNVERIFIED

The source wording, attribution, date, and numerical check were supplied by
the implementation brief. Source-to-Lean identification is not a
kernel-checked fact.
