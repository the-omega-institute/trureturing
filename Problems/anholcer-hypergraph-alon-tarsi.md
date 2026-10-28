---
slug: anholcer-hypergraph-alon-tarsi
bibkey: anholcer2026alontarsi
doi: 10.37236/15173
url: https://arxiv.org/html/2501.00157v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result
---

# The fixed-polynomial hypergraph Alon-Tarsi bound

## Problem

Conjectures 4 and 28 of Anholcer et al., *Electronic Journal of Combinatorics*
33(3), P3.74 (arXiv:2501.00157v2), assert AT(p) ≤ 2 ceil(ed(H)) + 1 for every
hypergraph polynomial, respectively every fully unbalanced hypergraph polynomial.
The field is arbitrary; multiple edges are allowed. Each edge has at least two
vertices and every incident coefficient is nonzero. Full unbalance requires two
unequal incident coefficients on each edge. Density counts induced occurrences
over nonempty vertex subsets, and AT uses nonzero maximum-total-degree monomials.

## Motivation

The proposed density bound applies to the supplied polynomial without coefficient
permutations. A fully unbalanced witness violating it addresses both universal
statements at once.

## Gap

The printed arbitrary-field statements allow characteristic three and repeated
edges. The native counterexample uses both allowances; characteristic-zero and
simple-hypergraph variants remain outside this refutation.

## Route

Three full edges on three vertices over F3, each with coefficients (1,1,-1),
are jointly admissible. The polynomial equals x^3+y^3-z^3 by Frobenius, so its
AT number is four, while its density is one and the proposed bound is three.

## Falsifier

The witness must satisfy the edge-size, nonzero-coefficient and full-unbalance
conditions jointly with the actual occurrence-indexed product, density one and
AT number four. Failure of any of these conditions would invalidate this
refutation. The native `source_counterexample` proves them for the same witness.

## Evidence

`D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.source_counterexample`
is the joint certificate, and
`D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result` negates the disjunction
of `Conjecture4` and `Conjecture28`. The closed universal predicates retain the
source field, vertex, edge-occurrence and coefficient parameters. The checked
axiom closure is `propext`, `Classical.choice` and `Quot.sound`.

## Triage

`theorem`. Both conjecture labels describe one related refutation family.
Theorem 1, which allows separate coefficient permutations, is outside this
refutation.

## ASSUMED-UNVERIFIED

Prior publication and global priority remain **ASSUMED-UNVERIFIED**; no claim of
priority is attached to the native proof.
