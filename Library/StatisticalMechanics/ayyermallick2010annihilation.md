---
bibkey: ayyermallick2010annihilation
authors: A. Ayyer and K. Mallick
year: 2010
title: "Exact results for an asymmetric annihilation process with open boundaries"
doi: 10.1088/1751-8113/43/4/045003
url: https://arxiv.org/abs/0910.0693
claim: "After Eq. (79): each eigenvalue seems to have exactly one eigenvector independent of the number of times the eigenvalue appears."
strata_touched:
  - D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1088/1751-8113/43/4/045003

Source: https://arxiv.org/abs/0910.0693

## Model and conjecture

A. Ayyer and K. Mallick, *Exact results for an asymmetric annihilation process
with open boundaries*, J. Phys. A 43, 045003 (2010). Page numbers for this
source refer to arXiv:0910.0693v2.

Section II, p. 2:

> We consider a nonequilibrium system on a finite lattice with L sites labelled
> from 1 to L.

> Empty sites are denoted by 0.

The displayed rules (1)–(3), p. 2, are:

> 10 → 01 with rate 1,
> 11 → 00 with rate λ.

> 0 → 1 with rate α,
> 1 → 0 with rate αλ.

> 1 → 0 with rate β.

The specialization λ = 1 makes the two bulk rates equal and makes the left
boundary a symmetric flip. A Boolean function on Fin L represents a state,
with true for a particle and index 0 for site 1. Bulk rates are added over
all bonds; left and right boundary rates are added when their moves have
the specified target state.

After Eq. (79), p. 14:

> We also conjecture that the Markov matrices are maximally undiagonalizable in
> the sense that each eigenvalue seems to have exactly one eigenvector independent
> of the number of times the eigenvalue appears (this implies that the Jordan
> blocks are of the maximum possible size). In other words, the degeneracy seems
> to be so strong that the Markov matrix M_L which is of size 2^L has only 2L
> eigenvectors.

The formal claim uses geometric multiplicity at most one for every real
eigenvalue, every positive length, and all positive real α and β. Restricting
to real eigenvalues is sufficient for the refutation at −2: at L = 5,
α = 1/3 and β = 2/5, the eigenspace has dimension at least two. The claim
does not assert existence of an eigenvector for a number outside the spectrum.

## Ayyer–Strehl restatement

A. Ayyer and V. Strehl, *The spectrum of an asymmetric annihilation process*,
FPSAC 2010, DMTCS Proc. AN, 461–472; DOI 10.46298/dmtcs.2884;
https://arxiv.org/abs/1008.2134v1.

Definition 1, p. 463 (PDF p. 3):

> A (continuous-time) transition matrix or Markov matrix or stochastic matrix is
> a square matrix of size equal to the cardinality of the configuration space
> whose (i, j)-th entry is given by the rate of the transition from configuration
> j to configuration i, when i is not equal to j. The (i, i)-th entry is then
> fixed by demanding that the entries in each column sum to zero.

Conjecture 1, p. 466 (PDF p. 6):

> The matrix M_L is maximally degenerate in the sense that it has exactly 2L
> eigenvectors.

Section 5, p. 471 (PDF p. 11):

> Our proof does not seem to explain the maximum amount of degeneracy, as stated
> in Conjecture 1.

Theorem 4 describes the characteristic polynomial. A geometric-multiplicity
counterexample does not contradict that characteristic-polynomial result.
