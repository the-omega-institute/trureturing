---
bibkey: parry1964intrinsicmarkov
authors: William Parry
year: 1964
title: Intrinsic Markov chains
doi: 10.1090/S0002-9947-1964-0161372-1
url: https://doi.org/10.1090/S0002-9947-1964-0161372-1
claim: The intrinsic Markov law gives the maximum-entropy probability for a primitive finite-type shift.
strata_touched:
  - D5/S3/TotalVariation/ParryKSMaximizer
license: citation-only
triage: anchor
---

# Intrinsic Markov chains

## Verified locator

The original bibliographic record is William Parry, *Transactions of the
American Mathematical Society* **112**, 55–66, DOI
[10.1090/S0002-9947-1964-0161372-1](https://doi.org/10.1090/S0002-9947-1964-0161372-1).

The measure-theoretic formulation is described in §2.3, pp. 323–324 of
*The mathematical research of William Parry FRS*. The survey states that the
intrinsic Markov measure is the unique probability attaining the maximum
entropy of a primitive finite-type shift.
[Institutional copy](https://wrap.warwick.ac.uk/id/eprint/682/1/WRAP_pollicott_Parry_research.pdf).

The forbidden-run relation space has suffix states from zero through (k-1).
Every state can reset to zero in one step. From zero, the path can wait at
zero and then increment to any target suffix in a total of (k) steps.
The suffix adjacency matrix is therefore primitive. In these coordinates,
the Perron transition has mass (pR_j/R_i) on an allowed edge from (i) to
(j), where (p) is the reciprocal Perron root and (R) is the positive
right eigenvector.

The Lean proof uses the native bilateral Boolean carrier, its measurable
suffix coding and the stationary Parry cylinders. The equality argument
covers invariant competitors with zero-mass legal words by applying the
finite log-sum and Gibbs equality laws to joint masses with their
absolute-continuity hypotheses.
