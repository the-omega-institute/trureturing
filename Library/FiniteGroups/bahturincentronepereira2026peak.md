---
bibkey: bahturincentronepereira2026peak
authors: Bahturin, Yuri; Centrone, Lucio; Pereira, Kauê
year: 2026
title: Quantum regularity of finite dimensional semisimple algebras
doi: 10.48550/arXiv.2608.21936
url: https://arxiv.org/abs/2608.21936v1
claim: Conjecture 31 asserts that every finite peak group is either solvable or a Frobenius group with the specified complement structure, exclusively.
strata_touched:
  - D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups
license: citation-only
triage: anchor
---

# Peak groups and Conjecture 31

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2608.21936

Source: https://arxiv.org/abs/2608.21936v1

## Source statements

Section 4, page 7, defines the character-degree set and peak groups:

> d(G) := {deg(χ) | χ is an irreducible character of G}. We say that G is a peak group if d(G) has the greatest element d with respect to the divisibility ordering.

Definition 28, page 11, states:

> Let G be a finite group with a neutral element e ∈ G and let H be a subgroup of G with {e} ⊊ H ⊊ G such that for any g ∈ G \\ H, H ∩ gHg^{−1} = {e}. Then H is called a Frobenius complement in G and G is called a Frobenius group.

Conjecture 31, pages 12–13, states:

> Let G be a peak group. Then, exactly one of the following holds:
> (1) G is a solvable group.
> (2) G is a Frobenius group with Frobenius complement H such that there exists a normal subgroup H0 of H/Fit(H) such that H0 ≅ SL(2, 5) × T, where T is a group satisfying the following conditions:
> (2.1) Every Sylow subgroup of T is cyclic.
> (2.2) p ∤ |T|, for any prime number p ∈ {2, 3, 5}.

The representation degrees are encoded by simple objects of `FDRep ℂ G` and
`Module.finrank ℂ`. The complement condition uses `H.map (MulAut.conj g)` for
conjugation. The Fitting subgroup is the supremum of normal nilpotent subgroups.
“Exactly one” is the conjunction of the disjunction and the negation of the conjunction.

## Scope

The proposed counterexample is the product of the source's semidirect product
of the additive group of the two-dimensional vector space over the field with eleven elements by
`SL(2, ZMod 5)` with a cyclic group of order two. A nonidentity central element
excludes every Frobenius complement. The representation-theoretic proof must
establish peakness of this actual finite group, independently of the conjecture.

The completeness of the literature screen is ASSUMED-UNVERIFIED.
