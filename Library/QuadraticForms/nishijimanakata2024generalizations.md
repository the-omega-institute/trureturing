---
bibkey: nishijimanakata2024generalizations
authors: M. Nishijima and K. Nakata
year: 2024
title: Generalizations of doubly nonnegative cones and their comparison
doi: 10.15807/jorsj.67.84
url: https://arxiv.org/abs/2204.12119
claim: "Conjecture 5.1 states that the NN-type generalized doubly nonnegative cone is contained in the BD-type cone for a direct product of a nonnegative orthant and second-order cones."
strata_touched:
  - D5/S3/QuadraticForms/ConicGDNN/Result
license: citation-only
triage: anchor
---

# Generalized doubly nonnegative cone inclusion

## Verified locator

DOI: 10.15807/jorsj.67.84

Source: https://arxiv.org/abs/2204.12119

Pinned version: https://arxiv.org/abs/2204.12119v4, Section 5.1, Conjecture 5.1.
Journal publication: *Journal of the Operations Research Society of Japan*
67(3) (2024), 84–109.

The source definitions used here are the zeroth homogeneous sum of squares
approximation in Theorem 3.5 with relaxation order zero, its dual in
Definition 3.6, and the BD-type cone in Definition 3.7. Section 4.2 also
considers products involving positive semidefinite cone factors; those
factors are outside the delivered Lean claim.

## Mathematical correspondence

For the product cone $K=\mathbb R_+^p\times\prod_{j=1}^r\mathcal L_{k_j+1}$,
the polynomial map is the Jordan square: orthant coordinates are squared,
and a Lorentz block $(t,z)$ maps to $(t^2+\|z\|^2,2tz)$.
The quartic sum of squares cone is the real convex hull of squares of
homogeneous quadratic polynomials. The symmetric trace dual of its matrix
pullback is the NN-type cone. The BD-type cone consists of positive
semidefinite matrices sending every extreme ray generator of $K^*$ into $K$.

`D5/S3/QuadraticForms/ConicGDNN/Result.result` proves the inclusion.
`D5/S3/QuadraticForms/ConicGDNN/Duality.mulVec_mem_cone` gives the stronger
preservation of every cone vector, including zero spatial dimensions.

The statement and definitions were read in arXiv:2204.12119v4. Exhaustive
literature completeness is ASSUMED-UNVERIFIED.
