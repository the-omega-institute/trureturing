---
bibkey: enagylaurentvarvitsiotis2012cycle
authors: Marianna E.-Nagy, Monique Laurent and Antonios Varvitsiotis
year: 2012
title: Complexity of the positive semidefinite matrix completion problem with a rank constraint
doi: null
url: https://arxiv.org/abs/1203.6602v2
claim: A real cycle correlation table has a PSD completion exactly when its closed spherical angles satisfy every odd-subset inequality; every feasible cycle table has a real completion of rank at most three.
strata_touched: []
license: citation-only
triage: anchor
---

# Cycle correlations and closed spherical polygons

Corollary 2.1, equation (5), characterizes membership in the cycle elliptope:
for a vector t in the closed cube [0,1] indexed by the cycle edges,
cos(pi t) belongs to the elliptope exactly when
sum(F,t) - sum(complement(F),t) is at most card(F)-1 for every odd-cardinality F.
The source attributes this criterion to Barrett, Johnson and Tarazaga.

The discussion following Lemma 2.1 states that every feasible cycle table on
at least four vertices has Gram dimension at most three. The preceding paragraph
includes the three-vertex elliptope, its boundary and its corners. The graph Gram
dimension also gives the same uniform rank bound: Laurent and Varvitsiotis,
*The Gram dimension of a graph*, arXiv:1112.5960v1, Lemma 3, states that partial
k-trees have Gram dimension at most k+1. A cycle is a partial 2-tree.

Set t(i)=arccos(a(i))/pi for arbitrary a(i) in [-1,1], and multiply the
inequalities by positive pi. Real unit vectors supply a real Gram matrix with
unit diagonal, the prescribed cyclic edges and rank at most three. Repeated
vectors, nonspanning configurations, zero or pi angles and singular matrices
are included. A realization or completion is a conclusion, not an input.

The formal construction eliminates two consecutive angles simultaneously,
realizes their closed spherical triangle, and aligns its endpoint pair with the
shorter polygon by an ambient isometry. This uses the original equal-Gram
isometry and rank-controlled factorization supplied in
`RankBoundedChordalPsdCompletion`; their attributed Apache-2.0 source and license
are documented in `laurentvarvitsiotis2014boundedrank.md`. No code is copied from
the arXiv texts. Both arXiv versions identify their license as the arXiv
perpetual non-exclusive license; they serve only as mathematical citations.

## Verified locator

- Main source: https://arxiv.org/abs/1203.6602v2
- Corollary 2.1 and equation (5): https://arxiv.org/html/1203.6602v2#S2.Thmcorollary1
- Independent rank bound: https://arxiv.org/html/1112.5960v1#Thmlemma3
