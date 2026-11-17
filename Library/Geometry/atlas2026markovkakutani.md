---
bibkey: atlas2026markovkakutani
authors: Unattributed source file; copyright Meta Platforms, Inc. and affiliates
year: 2026
title: Markov-Kakutani common fixed point theorem in ATLAS Lean
doi: null
url: https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/FunctionalAnalysis/MarkovKakutani.lean
claim: Every globally commuting family of continuous affine self-maps preserving a nonempty compact convex set in a real normed space has a common fixed point.
strata_touched:
  - D5/S3/Geometry/FixedPoint/MarkovKakutani
license: Complete upstream LICENSE including ML intended-use preface retained at docs/reports/lovasz-suppliers/atlas-LICENSE.txt
triage: anchor
---

# Markov-Kakutani common fixed point theorem

The exact formal supplier is `facebookresearch/atlas-lean` at immutable revision
`a60759060b5616df0d5775b42da4d337719feb32`, file
`MathlibExt/Analysis/FunctionalAnalysis/MarkovKakutani.lean`. Its SHA-256 is
`62353ec62e9ec6929cc2da8b9caccea4f2c944510305b2490fe3187566e899ad`.
The source file supplies no named author; Meta Platforms, Inc. and affiliates
is its stated copyright holder. The metadata year is the year of the pinned
repository revision, not an asserted original publication year.

The theorem covers every real normed vector space E and nonempty compact convex
set K in E. The index type is arbitrary, including empty. Each map is a
continuous affine self-map of E that maps K into itself. Commutation is required
globally on E. The result is one point in K fixed by all maps, with no
completeness, finite-dimensional, finite-family or linear-map restriction.
This is known classical mathematics, integrated for native Lean coverage.

The retained supplier has four private support theorems and one public endpoint.
Its single-map step uses Cesaro averages of iterates in K. Their affine
displacement telescopes to an endpoint difference divided by the averaging
length; compactness bounds that difference and yields a convergent subsequence.
Finite intersections of fixed loci follow by induction using commutation, then
compactness gives the common fixed point for the entire family. The native
adaptation changes the header, namespace and public declaration name while
retaining the proof bodies. No ATLAS Lake dependency is added.

The complete root license is retained at
`docs/reports/lovasz-suppliers/atlas-LICENSE.txt` with SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
That text includes a prefatory statement limiting intended use for ML model
development; this note records the actual terms without asserting blanket
permissive clearance.

Retire this transplant only if an adopted pinned Mathlib supplier provides the
full equivalent theorem for arbitrary families of continuous affine maps on a
nonempty compact convex set under global pairwise commutation. Prospective
common stationary vectors or affine symmetry applications are not measured
consumers or additional conclusions of this theorem.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/FunctionalAnalysis/MarkovKakutani.lean
contains `markovKakutani_commonFixedPoint` and its four consumed private
support theorems. The complete root license is at
https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/LICENSE.
