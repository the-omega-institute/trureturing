---
bibkey: lourenco2022amenable
authors: Bruno F. Lourenço, Vera Roshchina and James Saunderson
year: 2022
title: Amenable cones are particularly nice
doi: 10.1137/20M138466X
url: https://arxiv.org/html/2011.07745v2
claim: Every nice closed convex cone in a finite-dimensional real space is facially exposed.
strata_touched:
  - D5/S3/Quantum/Foundation/NiceConeFaces.every_face_exposed
license: citation-only
triage: anchor
---

# Niceness implies facial exposedness

## Verified locator

- Full text: https://arxiv.org/html/2011.07745v2, Section 2.2,
  Proposition 2.3, implication (iii) to (iv).
- DOI: https://doi.org/10.1137/20M138466X.
- Version: arXiv:2011.07745v2, 21 April 2022. The year in this note
  identifies that preprint version, not the journal publication year.

Section 2.2 defines niceness, also called facial dual completeness, by
$F^*=K^*+F^\perp$ for every face $F$ of the closed convex cone $K$.
Both dual cones consist of linear functionals on the same original
ambient real space, and the plus sign denotes a Minkowski sum.
Proposition 2.3 explicitly states that niceness implies facial
exposedness. Its proof attributes this implication to Theorem 3 of
reference [24]. The original locator is
https://arxiv.org/html/1202.4043v4, Pataki, Theorem 3(1).

## Correspondence and scope

`NiceConeFaces.Nice` uses precisely this ambient-dual identity, with
`F^perp` represented by annihilation of the real span of the original
face. The finite-dimensional real normed-space formulation uses the
same algebraic dual; it does not require a chosen inner product.
The formal conclusion provides an ambient real-linear functional
nonnegative on the original cone whose zero section is exactly the
specified original cone face. The whole face permits the zero
functional. In the maximizing convention of `IsExposed`, the exposing
functional has the opposite sign.

Lean's `PointedCone` means a cone containing zero and does not impose
the source's separate pointedness condition of zero lineality. The
formal theorem imposes neither salience nor full dimension; it
includes lineality, subspace cones and zero-dimensional ambient
spaces. Its native cone-face type contains zero and does not include
the empty face of a general convex set. The known implication does
not supply the other arrows in Proposition 2.3, a unit-preserving
projection, a uniform error-bound constant, moving-face regularity
or a physical quantum realization. The repository supplies a Lean
proof of the implication, not a claim of literature originality.
