---
bibkey: mukherjeeray2026connected
authors: Sanjay Mukherjee; Papi Ray
year: 2026
title: On the connected zero forcing polynomial of finite trees
doi: 10.48550/arXiv.2611.10985
url: https://arxiv.org/abs/2611.10985v1
claim: Problem 5.3 asks for a fixed ordered low-index <= and high-index >= coefficient crossing for every pair of same-order trees, without a common leaf count.
strata_touched:
  - D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation
  - D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder
license: CC-BY-4.0
triage: anchor
---

# Connected zero forcing polynomials of trees

## Verified locator

DOI: 10.48550/arXiv.2611.10985

https://arxiv.org/abs/2611.10985v1 ; primary HTML https://arxiv.org/html/2611.10985v1#S5.Thmtheorem3 ; PDF https://arxiv.org/pdf/2611.10985v1 . Version 1, Section 5, Problem 5.3, PDF page 21. The source HTML identifies the license as CC BY 4.0.

## Problem 5.3

> Given two trees T₁∈𝔗ₙ,ₚ₁ and T₂∈𝔗ₙ,ₚ₂, can we always find an integer l, with 1≤l≤n, such that Z_C(T₁,i)≤Z_C(T₂,i) for 1≤i≤l and Z_C(T₁,i)≥Z_C(T₂,i) for l+1≤i≤n?

The source family consists of all n-vertex trees with exactly p degree-one vertices. A connected zero forcing set is an ordinary zero forcing set whose initially induced subgraph is connected. Coefficients count vertex subsets of each cardinality. The fixed order and mandatory nonempty low segment are material. No initial swap, leaf-count ordering or global exclusion of paths is stated in the question.

## Source example and boundary

Section 4 already gives the four-vertex path and star, with coefficient lists (0,2,3,2,1) and (0,0,0,3,1). These data and examples are attributed to the authors. The formal refutation needs only the singleton coefficients, derived from the forcing semantics. The source's proved tree results and separate Problem 5.2 are outside this settlement. Authorial intent beyond the printed orientation is unverified.

## Smallest order of a counterexample

CrossingSmallestOrder.result states that the assertion restricted to trees of a fixed order n
holds exactly when n ≤ 3. All trees on at most three vertices are isomorphic to the path on as
many vertices and so have equal coefficients; at every order n ≥ 4 the path followed by the star
has no cutoff, since the path has two connected forcing sets of size one and the star none.
