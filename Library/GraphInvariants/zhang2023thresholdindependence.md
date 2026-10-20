---
bibkey: zhang2023thresholdindependence
authors: Erchuan Zhang
year: 2023
title: On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph
doi: 10.1016/j.dam.2025.07.017
url: https://arxiv.org/abs/2303.01024v1
claim: "Section 5 asks whether two T2-threshold k-hypergraphs with equal independence polynomials must be isomorphic."
strata_touched:
  - D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation
license: citation-only
triage: anchor
---

# Threshold hypergraphs and independence polynomials

## Verified locator

DOI: 10.1016/j.dam.2025.07.017

Source: https://arxiv.org/abs/2303.01024v1

The quoted text and page numbers refer to arXiv v1. The journal citation is
*Discrete Applied Mathematics* **378** (2026), 244–258; the final journal text
has not been checked.

## Source definitions

Page 2 states:

> A hypergraph H = (V, E) is an order pair of a set of vertices V and a set of
> hyperedges E, where each hyperedge e ∈ E is a non-empty subset of the vertex
> set V. Further, if |e| = k for any e ∈ E, then H is called k-uniform hypergraph,
> k-hypergraph or k-families.

Page 3 states:

> Motivated by this idea, a vertex subset W ⊆ V is called an independent set in a hypergraph H = (V, E)
> if W does not include any hyperedges, i.e., ∀e ∈ E, e ⊄ W.

Equation (8), p. 3, is

\[
I(H;x)=\sum_{W\subseteq V\text{ is independent in }H}x^{|W|}.
\]

Definition 4.1 (T2), p. 12, states:

> There exist a labeling c′ of V and a threshold τ′ such that, for any vertex
> subset X ⊆ V of size k, X ∈ E if and only if Σ_{x∈X} c′(x) > τ′.

## Closing question

Section 5, p. 18, states:

> One remaining question here is about the uniqueness of the independence
> polynomials of antiregular k-hypergraphs. Alternatively, a more general
> question is, given two T2-threshold k-hypergraphs with the same independence
> polynomial, are they isomorphic? These are left for future work.

The finite encoding uses an edge set of k-element finite vertex subsets,
real labels with a strict threshold, and vertex equivalences carrying edges
onto edges. The independence polynomial has integer coefficients and includes
the empty independent set. The encoded universal question allows all natural
k; the counterexample uses k = 3 and so belongs to the source's stated range.

## Scope and literature limitations

The repository refutation uses two five-vertex 3-hypergraphs. Their independent
subsets have the same cardinality profile; their vertex degrees differ. It does
not prove an arbitrary-size family or identify either hypergraph as antiregular.
The source's polynomial formulas and threshold theorems do not rely on a
positive answer to the closing question.

The literature screen recorded in issue #19406 checked arXiv v1, the author's
later works 2306.15180, 2502.02097 and 2609.12293, and related work 2602.21382.
That screen reported no settlement and zero citations in OpenAlex and Crossref.
MathDB was not located; the final subscription journal text was not read.
Completeness and worldwide priority remain **ASSUMED-UNVERIFIED**.
