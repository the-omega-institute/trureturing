---
bibkey: lamishirokov2023relativeentropy
authors: Ludovico Lami and Maksim E. Shirokov
year: 2023
title: Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme
doi: 10.1007/s00023-023-01313-1
url: https://doi.org/10.1007/s00023-023-01313-1
claim: Equations (2)-(5) on pages 4076-4077 give spectral entropy, the canonical nonnegative relative-entropy double series, and its energy interpretation.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy
license: citation-only
triage: anchor
---

# Canonical nonnegative quantum relative entropy

## Verified locator

L. Lami and M. E. Shirokov, Annales Henri Poincare 24 (2023),
4069-4137, pp. 4076-4077, equations (2)-(5).
DOI and published article: https://doi.org/10.1007/s00023-023-01313-1

## Correspondence and scope

Equation (3) defines relative entropy by the spectral transition-weight sum
of the nonnegative kernel p log p - p log q + q - p. The displayed formula
uses positive-eigenvalue indexing. The accompanying text states
D(0||0)=0, D(X||0)=infinity for nonzero X, and the necessary support
condition; it does not explicitly list every zero-fiber cell. The full-basis
interpretation uses g(0,q)=q, g(p,0)=infinity for positive p, and g(0,0)=0.
Zero transition weight times infinity is zero.

The application explained at the existing
`finiteEntropyRelativeEntropy_eq_energy_tsub` theorem uses arbitrary full
spectral resolutions of actual positive trace-class contractions on a
complete complex Hilbert space.
For trace-one arguments and finite self entropy, the sum equals the actual
bounded trace-log grid liminf already defined in the library. Cross energy
may be infinite. Neither faithfulness, commutation, separability, finite
dimension nor finite entropy of the second argument is assumed.

The proof sums the nonnegative balance

    g(p,q) + (-p log p) + p = p singularLog(q) + q

after applying ofReal to the finite nonnegative terms. Full-basis Parseval
gives both marginal masses one. Only finite trace mass and finite self
entropy are canceled. The correspondence is an established definition
identity; no new inequality or resolution of an external open problem is
claimed. The source article's Hilbert-space scope is not asserted to be a
verbatim arbitrary-index Lean statement. This explanation adds no public
canonical-series theorem or full positive-epsilon limit.
