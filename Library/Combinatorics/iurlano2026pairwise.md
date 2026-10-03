---
bibkey: iurlano2026pairwise
authors: Enrico Iurlano, Günther R. Raidl
year: 2026
title: "Pairwise Reflection Symmetry in Generalized Latin Rectangles"
doi: 10.48550/arXiv.2606.28315
url: https://arxiv.org/html/2606.28315v1
claim: "Definition 3 defines the joint row frequency and its reflection equality; Definitions 2 and 4 specify reduced arrays and the URS(n,lambda,mu) domain."
strata_touched:
  - D5/S3/Combinatorics/Graph/URSComponentParity
license: citation-only
triage: anchor
---

# Pairwise reflection symmetry and its source domain

## Verified locator

DOI: 10.48550/arXiv.2606.28315

URL: https://arxiv.org/html/2606.28315v1

The source is arXiv:2606.28315v1. The arXiv metadata identifies Enrico
Iurlano and Günther R. Raidl as the authors. This note cites the source
without reproducing its text.

## Definition and domain mapping

Definition 3 counts the rows simultaneously realizing prescribed symbols
in two prescribed columns. Pairwise reflection symmetry requires equality
of this count with the count obtained by exchanging the two symbols, for
every pair of distinct columns and every pair of distinct symbols. The
repository's `pairCount` is this joint row frequency on the single indexed
family `rho : Fin (2*n) -> Equiv.Perm (Fin n)`.

Definition 4 defines URS(n,lambda,mu) using lambda*n rows, mu*n columns,
uniform column multiplicity lambda, uniform row multiplicity mu, and
pairwise reflection symmetry. At lambda=2 and mu=1, the rows are
permutations, every column-symbol fibre has size two, and the source
reflection condition is precisely the joint-count hypothesis used by
`fibre_graph_connected`, after relabeling symbols and indices with `Fin`.

Definition 2 calls the mu=1 array reduced when its first row is the
identity tuple and its rows are in non-decreasing lexicographic order.
The connectivity theorem does not require either reduction condition,
so it also applies to this source-defined reduced domain.

## Attribution boundary

The joint frequency and URS domain are source-defined. The graph on
original row indices and its odd-order connectivity argument are
repository-derived. This citation attributes the domain and count;
it does not attribute a connectivity theorem to the source or establish
nonzero common-kernel existence, bipartiteness, a Latin-sheet
decomposition, or the source's counting and classification conjectures.
