---
slug: suvagiya-conjecture28-refutation
bibkey: suvagiya2026parity
doi: 10.48550/arXiv.2607.17343
url: https://arxiv.org/html/2607.17343v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.result
---

# Suvagiya Conjecture 28 refutation

## Problem

Conjecture 28 in section 12.3 of arXiv:2607.17343v2 states that for every
integer m >= 4, the minimum spectral radius over all independent edge
signings of C_(8m)(1,2) equals the greatest real root of
x^4−2x^3−6x^2+12x−4. The radius is the attained maximum absolute eigenvalue
of the real symmetric adjacency matrix. Both Hamilton-cycle sign products
are included.

## Motivation

The theorem `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.result`
negates that complete assertion. The concrete counterexample has 32 vertices
and does not belong to the periodic gauge slice supplying Theorem 26's
upper bound.

## Gap

The exact unrestricted optimum at n = 32 and at other sizes is not determined.
No repaired restriction on signings is proved.

## Route

The step-one signs are +1 except a_31 = −1. The step-two signs repeat
(1,1,−1,1,−1,−1,1,−1), with b_30 = −1 and b_31 = +1. Exact finite
Horner identities show R(A^2) = 0, where
R(y) = y^8−32y^7+416y^6−2816y^5+10568y^4−21632y^3+22168y^2−9408y+1262.
All coefficients of R((279/100)^2+z) are positive. Spectral mapping therefore
bounds the attained radius by 279/100. The quartic has a root between
279/100 and 3, since its endpoint values are −6766519/100000000 and 5.
Its greatest root is strictly larger than the radius of this signing.

## Falsifier

A discrepancy in any seam edge, failure of a finite Horner identity,
a nonpositive coefficient in the shifted polynomial, or a source restriction excluding independent
signings with Hamilton sign product −1 would invalidate the proposed
counterexample to this assertion.

## Evidence

The formal source defines the complete finite signing carrier, actual
symmetric adjacency, attained spectral radii, quartic roots, and closed
integer-indexed claim. Its sole public theorem is `result : Not claim`.
The mathematical statement is the unrestricted source conjecture, including
its attained extrema and complete sign domain.

The escape audit is unfinished ([issue #11789](https://github.com/the-omega-institute/trureturing/issues/11789)).
The faithful Reg mirror compiles, but registration processing reports
`IE-C050` (`E2.unknown_constant` at `LE.mk`). No `declared_validated`
registration or accepted source-binding evidence is established.

## Triage

The unrestricted lower bound is refuted; Theorem 26's upper bound is unaffected.
This is a Tier 1 named external conjecture, preregistered in issue 11744.
The admission basis is `open-problem-resolution`, the proof shape is
`bind-only`, and the escape witness is `none`. Its computational use is
`certified-instance` with `refutes` from `result` to `claim`.

## ASSUMED-UNVERIFIED

Exhaustive literature completeness and publication priority are unverified.
The Lean kernel verifies the formal proposition and proof; independent review
checks correspondence with the source's definitions and quantifiers.
