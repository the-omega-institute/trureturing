---
bibkey: meler2024weightedminors
authors: meler (MathOverflow user 526848; real name unverified)
year: 2024
title: Inequality involving minors of an orthogonal matrix
doi: null
url: https://mathoverflow.net/questions/469781
claim: The source asks the full weighted squared two-minor versus max-weighted squared three-minor inequality for every real orthonormal triple and every symmetric entrywise positive real matrix.
strata_touched:
  - D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors
license: CC-BY-SA-4.0
triage: anchor
---

## Verified locator

https://mathoverflow.net/questions/469781

Revision 1, GUID `F53D06CE-3805-43B9-9FEB-43A79F67F7AB`, by meler (MathOverflow user 526848), CC BY-SA 4.0. The identical crosspost is https://math.stackexchange.com/questions/4902019. The supplied immutable question transcription establishes this locator, attribution, revision and license; the author's real name is unverified. The metadata publication year 2024 is ASSUMED-UNVERIFIED: the supplied transcription omits the publication timestamp.

## Mathematical scope

The source fixes any integer n at least three and any real orthonormal vectors x,y,z. For every real symmetric matrix A with strictly positive entries it asks whether the sum of A(i,j) times the squared two-by-two coordinate determinant over i<j is at most the sum of max(A(i,j),A(i,k),A(j,k)) times the squared three-by-three coordinate determinant over i<j<k. Positivity is entrywise; positive definiteness and distance-matrix conditions are absent. Dimension three, zero minors, equal weights and equality are included. The complete question and its exact Lean correspondence are in [the dossier](../../Problems/mathoverflow-469781-weighted-orthogonal-minors.md).

The question supplies the assertion, not the completed proof. `AlternatingArrayContraction.weighted_minors` is the repository's direct finite-array synthesis. It uses an adjoint/energy identity, unit-vector contraction, coordinate-family projection locality, an exact finite upper-threshold expansion, and ordered-pair/triple multiplicities two and six. It directly calls pinned Mathlib finite squared Cauchy-Schwarz and determinant expansions; it assumes no determinantal coupling or Hall inequality.

## Literature boundary

The bounded source reading recorded in [issue #25537](https://github.com/the-omega-institute/trureturing/issues/25537) covers both complete question threads and revisions, seven MSE comments and the MO crosspost comment; that reading reported no posted answer. It also covers Russell Lyons, *Determinantal probability measures*, [arXiv:math/0204325v4](https://arxiv.org/pdf/math/0204325v4), sections 4, 5, 6 and 10. Theorem 6.2 gives stochastic ordering for projection-determinantal laws of nested finite subspaces. This is relevant established context, not a Lean premise of the direct array proof and not an attestation of the exact weighted conclusion.

The same supplied reading covers Bistroń, Eckstein, Friedland, Miller and Życzkowski, *A new class of distances on complex projective spaces*, [arXiv:2312.02583v1](https://arxiv.org/pdf/2312.02583v1), definitions/Conjecture 2.1, Theorem 4.1, Corollaries 4.2/4.7 and Theorems 6.3/6.4/6.8. Its projective-distance triangle question and restricted distance/operator results do not themselves state this arbitrary-positive-weight assertion. No paper text is reproduced here. No exhaustive literature absence, worldwide openness, priority or author-acceptance claim is made.
