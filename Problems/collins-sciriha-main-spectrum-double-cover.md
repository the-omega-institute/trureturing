---
slug: collins-sciriha-main-spectrum-double-cover
bibkey: collinssciriha2019main
doi: 10.48550/arXiv.1906.05790
url: https://arxiv.org/abs/1906.05790v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.result
---

# Isomorphic canonical double covers preserve the main spectrum

## Problem

Luke Collins and Irene Sciriha, *On the Walks and Bipartite Double Coverings of Graphs with the same Main Eigenspace*,
arXiv:1906.05790v1, DOI 10.48550/arXiv.1906.05790, Question 5.8, p. 15, ask:

> Let G and H be two graphs with CDC(G) ≃ CDC(H). Do G and H have the same main eigenvalues?

Irene Sciriha and Luke Collins, *The walks and CDC of graphs with the same main eigenspace*,
DOI 10.7151/dmgt.2386, ask the same question as Question 16, p. 522.
The canonical double cover is the direct product with the complete graph
on two vertices. A real adjacency eigenvalue is main if its eigenspace
has a vector with nonzero inner product with the all-ones vector.

For all finite simple undirected graphs G and H on independently typed
vertex sets, all graph isomorphisms between their canonical double covers,
and every real λ, prove both implications between mainness of λ for G
and mainness of λ for H. In the Lean predicate the inner product with the
all-ones vector is the sum of the real eigenvector coordinates.

## Motivation

The main spectrum records the adjacency eigenvalues visible from the
all-ones vector. The question asks whether the isomorphism type of the
cover determines this set for the base graph.

## Gap

Journal Remark 17 reports that no counterexample was found on at most
eight vertices. Mizzi, arXiv:2603.27559v4, §7, explicitly calls the
question open. Issue #31874 records the source and literature check for
the quantified claim. Teranishi's general equitable-quotient theorem,
credited and reproved by Yan and Wang in arXiv:2201.01101v1, Lemma 3,
gives the method.

## Route

On the disjoint sum of two copies of the base vertex type the cover
adjacency sends a pair of vectors to the pair obtained by applying base
adjacency to the opposite layer in each coordinate. Duplicating a base
eigenvector into both layers therefore preserves the eigenvalue and doubles
its coordinate sum. Adding the layers of a cover eigenvector yields a base
eigenvector at the same eigenvalue and preserves the coordinate sum.
These are the two maps of the equitable quotient by the two-vertex fibers.

A graph isomorphism reindexes adjacency multiplication and preserves the
sum over all vertices. Lift from one base graph, reindex across the
covers, and sum the layers of the other cover. Apply the same argument
with the inverse isomorphism for the reverse implication.

## Falsifier

Two finite simple graphs with isomorphic canonical double covers and a
real eigenvalue that is main for exactly one would refute the assertion.

## Evidence

The affirmative statement is D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.result.
The definition D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.IsMain uses a real adjacency
eigenvector with a nonzero coordinate sum.

## Triage

### What the settlement shows

- **Proved** by `D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.result`.
  The main spectrum is the same on any two bases with isomorphic covers.
  The lift and fiber sum preserve the eigenvalue and nonvanishing of the
  sum, and the isomorphism may mix the two layers.
- **Proved scope** of the same GID. The graph types may be empty and the
  graphs may be disconnected. The argument applies at zero and every
  other real parameter. For an empty vertex set the existential mainness
  predicate is false since every coordinate sum is zero.
- **Proved consequence** of the same GID. The implication asked in the
  source's Figure 7 holds without the eight-vertex restriction in
  Remark 17. Its scope is equality of the sets of main eigenvalues.
  Mizzi's independent enumeration of connected graphs and questions on
  TF-cousin counts and unstable graphs are outside this consequence.
- **Open here.** Equality or identification of principal main eigenvectors
  or of the main eigenspaces of the two base graphs is a different
  conclusion. An arbitrary isomorphism of the covers need not provide a
  vertex bijection of the bases compatible with both fiber partitions.

## ASSUMED-UNVERIFIED

Worldwide priority is unverified. Issue #31874 records the examined
later literature and the HTTP 403 boundary for the Huang–Huang–Lu
journal text. The source's eight-vertex check is a cited result.
