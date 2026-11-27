---
slug: akbari-elahimanesh-miraftab-nontransitive-adjacency-factors
bibkey: akbari2025primematrixproduct
doi: 10.48550/arXiv.2512.24864
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors.result
---

# Non-vertex-transitive adjacency factors of a complete graph

## Problem

Saieed Akbari, Mohamad Parsa Elahimanesh and Bobby Miraftab ask in
*On Prime Matrix Product Factorizations*, arXiv:2512.24864v1, §5 item 2:

> We ask the following: find two non-transitive graphs $H$ and $K$ with adjacency matrices $B$ and $C$ respectively such that $BC=J-I$.

The preceding sentence describes factorizations of complete graphs with transitive factors.
Here transitivity means vertex transitivity. The two finite simple undirected
graphs share one labelled vertex set, $J$ is the all-ones matrix, and $I$ is the
identity. The product is ordinary multiplication of integer matrices.
[Published question](https://arxiv.org/html/2512.24864v1#S5.I1.i2) · [Source note](../Library/AdjacencyProduct/akbari2025primematrixproduct.md)

| Source clause | Lean counterpart |
| --- | --- |
| Find graphs $H$ and $K$ on a common finite carrier | Existentially quantified `H K : SimpleGraph (Fin 17)`. Order 17 is a choice of witness for the unrestricted existence question. |
| Their adjacency matrices $B$ and $C$ | `H.adjMatrix ℤ` and `K.adjMatrix ℤ`, with decidable adjacency obtained with the witnesses. |
| Ordinary product $BC=J-I$ | `H.adjMatrix ℤ * K.adjMatrix ℤ = Matrix.of 1 - 1`. |
| Both factors are non-transitive | Each graph separately satisfies the negation of the statement that for every pair of vertices, a graph automorphism sends the first to the second. |

## Motivation

The two factors are regular, so vertex degree alone cannot distinguish their
automorphism orbits. Their closed-walk counts give obstructions at different
lengths.

## Gap

The complete-graph factorability criterion gives the orders admitting some
factorization. The published question asks whether both factors can fail
vertex transitivity in the same factorization. The unrestricted question and
the bounded order-17 witness search are registered in the linked issues.
[Question registration #34958](https://github.com/the-omega-institute/trureturing/issues/34958) · [Witness registration #34961](https://github.com/the-omega-institute/trureturing/issues/34961)

## Route

The D5 source defines the two factors by their literal neighbor lists.
For each ordered pair `(i, j)`, the `(i, j)` entry of $BC$ is the sum
over intermediate vertices adjacent to $i$ in $H$ and to $j$ in $K$.
The certificate checks that it is zero when $i=j$ and one otherwise.

An automorphism reindexes the adjacency matrix to itself. Matrix reindexing
along a vertex permutation commutes with powers, so the diagonal entry of
each power is constant on each automorphism orbit. In $H$, the length-three
closed-walk counts are 2 at vertex 0 and 0 at vertex 1. In $K$, the length-four
counts are 40 at vertex 0 and 42 at vertex 2. The two inequalities rule out
vertex transitivity of the respective factors.

## Falsifier

The witness would fail if a neighbor relation had a loop or lacked symmetry,
if any of the 289 product entries disagreed with $J-I$, or if the two selected
diagonal entries for either factor were equal. The argument also requires
that the claimed graph automorphisms preserve these diagonal entries.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors.result`.
The proof uses the pinned Mathlib adjacency-matrix reindexing lemma
`SimpleGraph.Embedding.submatrix_adjMatrix` and the multiplication identity
`Matrix.submatrix_mul_equiv` for reindexing by a bijection. The correspondence between diagonal powers and
closed-walk counts is `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`.
The finite checks use kernel `decide`.
The witness tables and exact arithmetic readings appear in the witness issue.
[Witness and independent replay](https://github.com/the-omega-institute/trureturing/issues/34961)

## Triage

The result gives a positive existential resolution of §5 item 2 under
`admission_basis: open-problem-resolution`. It supplies a factor pair on
17 vertices. Minimum order and classification of such factorizations are
outside the published existence question.

## ASSUMED-UNVERIFIED

Literature completeness and independent priority are unverified. The
registration records the scoped search and its coverage limits.
[Prior-solution search #34958](https://github.com/the-omega-institute/trureturing/issues/34958)
