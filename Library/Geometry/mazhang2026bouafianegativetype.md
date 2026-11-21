---
bibkey: mazhang2026bouafianegativetype
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Negative answers to Bouafia's Open problem: a five-point example and an exponential-similarity extension of Huntsman (2026)"
doi: "10.5281/zenodo.24212421"
url: "https://doi.org/10.5281/zenodo.24212421"
claim: "Proposition 2: for symmetric positive definite Z and a probability vector p, p minimizes E(p) = p^T Z p on the simplex iff (Zp)_i = E(p) when p_i > 0 and (Zp)_j >= E(p) for all j."
strata_touched:
  - D5/S3/Geometry/Diversity/SimplexQuadraticOptimality
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Geometry/mazhang2026bouafianegativetype -->
# Simplex optimality for diversity energies

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, version 2, exact-version DOI
https://doi.org/10.5281/zenodo.24212421 (concept DOI 10.5281/zenodo.24212420), Proposition 2,
Section 3. The question answered by the note is Philippe Bouafia, arXiv:2605.03681v1,
Section 4.1, p. 18, recorded in bouafia2026treemagnitude.

## Statement

Let Z be symmetric positive definite and p a probability vector. Then p minimizes
E(p) = p^T Z p over the probability simplex if and only if (Zp)_i = E(p) whenever p_i > 0 and
(Zp)_j >= E(p) for every j. The note states that this reproves Bouafia's Proposition 3 in the
finite positive-definite setting; it is the first-order optimality condition for a convex
quadratic program on the simplex. Necessity comes from the feasible directions e_j - p, and
the weighted average of (Zp)_j - E(p) with weights p_j vanishes, forcing equality on the
support; sufficiency comes from convexity of E.
