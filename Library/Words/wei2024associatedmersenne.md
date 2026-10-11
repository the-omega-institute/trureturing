---
bibkey: wei2024associatedmersenne
authors: J. Wei and Y. Yang
year: 2024
title: Associated Mersenne graphs
doi: 10.48550/arXiv.2407.08237
url: https://arxiv.org/abs/2407.08237v1
claim: Questions 6.2 and 6.3 concern degree counts and cube polynomials of the Associated Mersenne graphs.
strata_touched:
  - D5/S1/Words/AssociatedMersenne/CircularWords
  - D5/S1/Words/AssociatedMersenne/RunTupleBijection
  - D5/S1/Words/AssociatedMersenne/SingleRunDegrees
  - D5/S1/Words/AssociatedMersenne/MultiRunDegrees
  - D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration
  - D5/S1/Words/AssociatedMersenne/TransferTuples
  - D5/S1/Words/AssociatedMersenne/TransferResolvent
  - D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction
  - D5/S3/Combinatorics/Hamming/InducedSubcubes
  - D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial
license: citation-only
triage: anchor
---

# Associated Mersenne graphs

## Verified locator

DOI: 10.48550/arXiv.2407.08237

Source: https://arxiv.org/abs/2407.08237v1

## Definition

The definition occurs on pages 3–4 of arXiv v1, Section 1 (source lines 201–206):

> A string of $\mathbf{B}_{n}$ is called *run-constrained-circularly* if every run of 1s appearing in this string is immediately followed by a strictly longer run of 0s in a circular manner. Let $\mathbf{M}_{n}$ be the set of all such words of length $n$. Then the *associated Mersenne graph* $\mathcal{M}_{n}$ is defined on the vertex set $\mathbf{M}_{n}$, and two vertices adjacent if and only if their Hamming distance is 1. For convenience, we also set $\mathbf{M}_{0}=\{\lambda\}$ and $\mathbf{M}_{1}=\{0\}$.

Words are labelled Boolean functions on `Fin n`; rotations preserve the labelled graph rather than identify vertices. `IsOneRunStart` includes length zero. Positive run marks satisfy `IsMarkedStart := ∃ r > 0, IsOneRunStart w i r`. The admissibility predicate excludes the all-ones word when `n > 0` and requires at least `r+1` zeros after each run of `r` ones.

## Structural results

Lemmas 3.5 and 3.6, on pages 9–10 (source lines 600–640), analyze neighbouring run-constrained circular words and deletion of a 1 from an initial run. These are source context; the degree classification here treats all circular gaps, including the case in which both endpoints meet the same run.

## Question 6.2

On page 18 the source states:

> The nature of the degree sequences of Fibonacci-run graphs $\mathcal{R}_{n}$ was considered [EI2], and a refinement of the generating function of the degree sequences $\mathcal{R}_{n}$ was obtained. In relation to this, a natural question is raised as the following.
>
> **Question 6.2.** For given $n$ and $k$, how many vertices of Associated Mersenne graph $\mathcal{M}_{n}$ have degree $k$?

The formal answer uses the degree series with coefficients in `Polynomial ℤ`: its coefficient of `x^n y^k` counts degree-`k` vertices. The equality `degSeries * DEN = NUM` uses explicit polynomial coefficients and includes lengths zero, one and two.

The marked run decomposition gives ordered tuples `(r_i,s_i)` of positive run lengths and nonnegative slack, with total length `Σ(2r_i+1+s_i)`. Periodic words remain included. The transfer trace uses an exact singleton correction: for `[(r,1)]`, the provisional degree is `min r 2 + 1`, whereas the tuple degree is `min r 2`. The correction is `X * (1 - Y) * Rser` before marking and `X * derivative (X * (1 - Y) * Rser)` after marking.

## Question 6.3

On page 18 the source states:

> **Question 6.3.** What is cube polynomial for Associated Mersenne graph $\mathcal{M}_n$?

The settlement gives the cleared-denominator generating function for the cube polynomials, with the endpoint-removal and marked-block argument recorded in the corresponding D5 modules.

## Boundaries

The journal version is Graphs and Combinatorics 41 (2025), article 73, DOI 10.1007/s00373-025-02936-3. Its full text has not been verified; the assertion that it leaves Question 6.2 open is ASSUMED-UNVERIFIED. The asymptotic distribution and degree moments are follow-up questions, and Question 6.1 on Hamiltonicity is open here.
