---
bibkey: anholcer2026alontarsi
authors: M. Anholcer, B. Bosek, G. Gutowski, M. Lasoń, J. Przybyło, O. Serra, M. Tuczyński, L. Vena and M. Zając
year: 2026
title: Alon-Tarsi for Hypergraphs
doi: 10.37236/15173
url: https://arxiv.org/html/2501.00157v2
claim: Conjectures 4 and 28 give a fixed-polynomial Alon-Tarsi bound over arbitrary fields; one fully unbalanced characteristic-three multihypergraph refutes both.
strata_touched:
  - D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation
license: citation-only
triage: anchor
---

# Alon-Tarsi for Hypergraphs

## Locator

The version of record is *Electronic Journal of Combinatorics* 33(3), P3.74,
DOI 10.37236/15173, published 2026-09-25. The corresponding preprint is
[arXiv:2501.00157v2](https://arxiv.org/html/2501.00157v2).
Journal PDF page numbers are used below.

## Statements and native scope

Conjecture 4 (pp. 5 and 23) asserts that every hypergraph polynomial p of H
satisfies AT(p) ≤ 2 ceil(ed(H)) + 1. Conjecture 28 (p. 23) asserts the same
bound for every fully unbalanced hypergraph polynomial of every H.
These statements concern the supplied polynomial, without coefficient permutations.

The definitions on p. 6 allow arbitrary fields and repeated edges, require
finite vertex and edge sets and edges of size at least two, and require each
incident coefficient a[e,v] to be nonzero. An edge is unbalanced when its
coefficients are not all equal. Density is the maximum of |E(X)|/|X| over
nonempty vertex subsets X, where E(X) counts induced edge occurrences.
The AT number minimizes the largest individual exponent plus one over nonzero
formal monomials of maximum total degree. It is not a polynomial-function invariant.

The native declaration `source_counterexample` supplies three occurrences of the
full three-vertex edge over F3, with coefficients (1,1,-1) on each occurrence.
The indexed product is (x+y-z)^3 = x^3+y^3-z^3, density is one, total degree
is three, and AT is four. The declaration `result` negates the disjunction of
the two complete universal predicates, whose coefficients may depend on both
edge occurrence and vertex. This is one related refutation family.

This result does not settle characteristic-zero or simple-hypergraph variants,
or contradict Theorem 1, which permits separate coefficient permutations.
Prior publication and global priority remain **ASSUMED-UNVERIFIED**. The source
still posing the statements as conjectures and bounded index searches do not
establish priority; no priority claim is made.
