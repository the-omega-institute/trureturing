---
bibkey: kraussimanek2024polynomialcontent
authors: A. Kraus and B. Simanek
year: 2024
title: New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar
doi: 10.1007/s10659-024-10087-4
url: https://arxiv.org/abs/2309.16450
claim: Conjecture 2.1 asserts that for every polynomial degree there is a polygon side count for which the unit-area polynomial content has no maximizer.
strata_touched:
  - D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation
  - D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/s10659-024-10087-4

Source: https://arxiv.org/abs/2309.16450

## Source statement

arXiv:2309.16450v1, p. 3, Conjecture 2.1:

> For each N ∈ ℕ, there is an n ∈ ℕ so that among all n-gons with area 1, ρ_N has no maximizer.

Section 1, p. 2, characterizes the polynomial content:

> Notice that ρ_N(Ω) is the square of the distance from z̄ to P_N in L²(Ω, dA)

Here P_N is the space of polynomials of degree at most N. Section 2 considers
simply connected Jordan regions in the complex plane. Theorem 2.2 states:

> Among all hexagons with area 1, ρ₁ and ρ₂ have no maximizer.

The Lean polygon index n represents n + 3 sides. The area is planar volume;
the polynomial content is the infimum of the squared integral approximation
errors over complex polynomials of degree at most N.

## Scope

The star construction with m = max(3, N + 2) gives unit-area 2m-gons with
unbounded degree-N polynomial content. The rotational symmetry cancels the
complex moments through order N + 1, and stretching increases the polar
second moment. The minimal number of sides is a separate question.

## Literature boundary

The arXiv v1 source is the statement source. The J. Elasticity article body
and the full Baylor dissertation of Kraus are unread; whether either gives
a settlement for N ≥ 3 is ASSUMED-UNVERIFIED. Literature completeness is
ASSUMED-UNVERIFIED. The source's degree-one and degree-two hexagon result
is not claimed as new.
