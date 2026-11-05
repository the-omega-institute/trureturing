# Reverse level order labeling of a tree

## Abstract

A labeling that decreases with distance from a tree's root gives exactly one nonzero entry in every column tail before the last column.

**Definition 1.1 (The column-tail property).**

$$(\operatorname{D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(g\right)\right)], ((\operatorname{SimpleGraph.IsTree}\left(g\right)) \to (\forall (r: \operatorname{Fin}\left(n\right)), (\forall (l: \operatorname{Equiv}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)), ((\left(\operatorname{StrictAnti}_{\operatorname{Preorder.lift}\left(\operatorname{SimpleGraph.dist}\left(g, r\right)\right), \operatorname{inferInstance}}\right)\left(\operatorname{DFunLike.coe}\left(l\right)\right)) \to (\forall (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin.val}\left(i\right) + (1: \mathbb{N}) < n) \to (\exists! (j: \operatorname{Fin}\left(n\right)), ((i < j) \land (\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{N}, g, \operatorname{DFunLike.coe}\left(\operatorname{Equiv.symm}\left(l\right)\right)\left(j\right), \operatorname{DFunLike.coe}\left(\operatorname{Equiv.symm}\left(l\right)\right)\left(i\right)\right) \ne (0: \mathbb{N})))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Olga Leskovjanová; Ladislav Mišta Jr. (2025). *Minimal criteria for continuous-variable genuine multipartite entanglement*. DOI: [10.22331/q-2025-08-27-1837](https://doi.org/10.22331/q-2025-08-27-1837). URL: <https://arxiv.org/abs/2401.04376v3>.

*Commentary.*

Let g be a tree on Fin n, let r be any root, and let l be a bijection from its vertices to Fin n. The order on the domain of StrictAnti is the preorder lifted along the distance from r; the order on its codomain is the usual order on Fin n. Thus smaller distance requires a larger label, with no restriction on the relative labels within a level. The explicit DFunLike.coe applications regard the bijections as functions, and Fin.val i is the natural-number value of i. For each i with Fin.val i + 1 < n, exactly one row j larger than i has a nonzero adjacency entry at the vertices with labels j and i. The adjacency matrix takes values in the natural numbers. Section 4.1.3 of the source, Quantum-accepted.tex lines 828–835, chooses a central root and labels the levels in decreasing order; lines 837–839 conjecture this column-tail property. Here the labels 0 through n minus one correspond to the source's labels 1 through n, and the statement permits every root and every order within a level.

**Theorem 1.2 (Exactly one nonzero entry in each column tail).**

$$\forall (n: \mathbb{N}), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(g\right)\right)], ((\operatorname{SimpleGraph.IsTree}\left(g\right)) \to (\forall (r: \operatorname{Fin}\left(n\right)), (\forall (l: \operatorname{Equiv}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)), ((\left(\operatorname{StrictAnti}_{\operatorname{Preorder.lift}\left(\operatorname{SimpleGraph.dist}\left(g, r\right)\right), \operatorname{inferInstance}}\right)\left(\operatorname{DFunLike.coe}\left(l\right)\right)) \to (\forall (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin.val}\left(i\right) + (1: \mathbb{N}) < n) \to (\exists! (j: \operatorname{Fin}\left(n\right)), ((i < j) \land (\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{N}, g, \operatorname{DFunLike.coe}\left(\operatorname{Equiv.symm}\left(l\right)\right)\left(j\right), \operatorname{DFunLike.coe}\left(\operatorname{Equiv.symm}\left(l\right)\right)\left(i\right)\right) \ne (0: \mathbb{N}))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.result` (`✓ std3`). ∎

*Resolves.* `Problems/leskovjanova-mista-2025-reverse-level-order-tree-labeling` (proved) by `D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"leskovjanova-mista-2025-reverse-level-order-tree-labeling","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Olga Leskovjanová; Ladislav Mišta Jr. (2025). *Minimal criteria for continuous-variable genuine multipartite entanglement*. DOI: [10.22331/q-2025-08-27-1837](https://doi.org/10.22331/q-2025-08-27-1837). URL: <https://arxiv.org/abs/2401.04376v3>.

*Commentary.*

First fix a vertex v distinct from r and take a shortest walk p from v to r. Write its first edge as v to w and its remaining walk as q from w to r. The distance from r to w is at most the length of q, while the length of q plus one equals the distance from r to v. Along an edge of a tree the two distances from r differ by exactly one. These facts force the distance from r to w plus one to equal the distance from r to v.

If u is another neighbor of v whose distance from r plus one equals the distance from r to v, take a shortest walk s from u to r. Prepending the edge from v to u makes a walk whose length equals the distance from v to r. It is therefore a path, as is p. A tree has a unique path between these endpoints, so the two paths agree. Their vertices at position one are u and w, which must be equal. Thus each vertex distinct from r has a unique neighbor one level nearer r.

Next consider adjacent vertices v and w. Their levels differ by one. If l(v) < l(w), the alternative that w is one level farther from r would give l(w) < l(v) by strict antitonicity, a contradiction. Hence w is one level nearer r. Conversely, if w is one level nearer r, strict antitonicity gives l(v) < l(w). Larger labels among neighbors therefore characterize the parent.

Now fix i with Fin.val i + 1 < n. The vertex with label i cannot be r. Indeed, suppose it were r and let j be the element of Fin n with value Fin.val i + 1. Injectivity of the inverse labeling ensures that the vertex with label j differs from r. Its distance from r is positive, whereas the distance from r to itself is zero. Strict antitonicity would give j < i, contradicting the choice of j.

For the vertex with label i, take its unique parent w and set j = l(w). The label comparison gives i < j, and symmetry of adjacency makes the matrix entry in row j and column i equal to one. For any row j larger than i with a nonzero entry, the corresponding vertex must be adjacent to the vertex with label i, since a nonadjacent entry is zero. The label comparison makes that vertex a parent, so uniqueness identifies it with w. Applying l identifies its row label with l(w). This proves existence and uniqueness for every required column.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.result`
