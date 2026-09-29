# Acyclic orientations of complete tripartite graphs modulo 4

## Abstract

For all m, n, p at least 1 that are not all odd, the complete tripartite graph K_{m,n,p} has a number of acyclic orientations congruent to 2 modulo 4, as conjectured by L. Mühlherr and G. Poullot (clause (4) of Conjecture 1 of arXiv:2609.02249). The number of acyclic orientations of a graph is its Tutte polynomial at (2, 0), the q = -1 point of the Potts model.

**Definition 1.1 (Orientations).**

$$\operatorname{IsOrientation}\left(G, d\right) \Leftrightarrow (\forall a \in V,\; \forall b \in V,\; \operatorname{d}\left(a, b\right) = \operatorname{true} \Leftrightarrow (\operatorname{Adj}\left(G, a, b\right) \land \operatorname{d}\left(b, a\right) = \operatorname{false}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.IsOrientation` (`✓ std3`).

*Citation.* Leonie Mühlherr; Germain Poullot (2026). *Hamiltonicity of graphs of acyclic orientations and acyclic polynomials*. URL: <https://arxiv.org/abs/2609.02249v2>.

*Commentary.*

A Boolean relation d on the vertices orients the simple graph G when every edge {a, b} carries exactly one of the arcs a to b and b to a, and no other pair carries an arc.

**Definition 1.2 (Acyclic relations).**

$$\operatorname{IsAcyclic}\left(d\right) \Leftrightarrow (\forall a \in V,\; \neg(\operatorname{TransGen}\left(((x, y) \mapsto \operatorname{d}\left(x, y\right) = \operatorname{true}), a, a\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.IsAcyclic` (`✓ std3`).

*Citation.* Leonie Mühlherr; Germain Poullot (2026). *Hamiltonicity of graphs of acyclic orientations and acyclic polynomials*. URL: <https://arxiv.org/abs/2609.02249v2>.

*Commentary.*

The relation has no directed cycle: no vertex is related to itself by the transitive closure of the arcs.

**Definition 1.3 (The number of acyclic orientations).**

$$\operatorname{acyclicOrientationCount}\left(G\right) = \left|\{d: V \to V \to \operatorname{Bool} \mid \operatorname{IsOrientation}\left(G, d\right) \land \operatorname{IsAcyclic}\left(d\right)\}\right|$$

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.acyclicOrientationCount` (`✓ std3`).

*Citation.* Leonie Mühlherr; Germain Poullot (2026). *Hamiltonicity of graphs of acyclic orientations and acyclic polynomials*. URL: <https://arxiv.org/abs/2609.02249v2>.

*Commentary.*

psi(G) is the number of acyclic orientations of G, counted as Boolean relations on the vertex set.

**Definition 1.4 (Clause (4) of Conjecture 1).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; 1 \le m \Rightarrow (1 \le n \Rightarrow (1 \le p \Rightarrow (\neg(\operatorname{Odd}\left(m\right) \land \left(\operatorname{Odd}\left(n\right) \land \operatorname{Odd}\left(p\right)\right)) \Rightarrow (\operatorname{acyclicOrientationCount}\left(\operatorname{completeMultipartiteGraph}\left(((i : \operatorname{Fin}\left(3\right)) \mapsto \operatorname{Fin}\left([m, n, p](i)\right))\right)\right) \operatorname{mod} 4 = 2)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.claim` (`✓ std3`).

*Citation.* Leonie Mühlherr; Germain Poullot (2026). *Hamiltonicity of graphs of acyclic orientations and acyclic polynomials*. URL: <https://arxiv.org/abs/2609.02249v2>.

*Commentary.*

For all m, n, p at least 1 that are not all odd, the complete tripartite graph K_{m,n,p}, Mathlib's complete multipartite graph over the family i ↦ Fin([m, n, p](i)) indexed by Fin 3, that is with parts Fin m, Fin n and Fin p, in which two vertices are adjacent exactly when they lie in different parts, has psi congruent to 2 modulo 4.

**Theorem 1.5 (Proof of clause (4)).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.result` (`✓ std3`). ∎

*Resolves.* `Problems/muhlherr-poullot-2026-tripartite-acyclic-orientations` (proved) by `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"muhlherr-poullot-2026-tripartite-acyclic-orientations","declaration_gid":"D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Leonie Mühlherr; Germain Poullot (2026). *Hamiltonicity of graphs of acyclic orientations and acyclic polynomials*. URL: <https://arxiv.org/abs/2609.02249v2>.

*Commentary.*

If two commuting involutions r and s of a finite set act without fixed points, and so does r s, the orbits have four elements and 4 divides the size of the set. For non-adjacent vertices u and v with the same neighbours and an edge avoiding both, take r the reversal of all arcs and s the swap of u and v on the acyclic orientations: r has no fixed point because the graph has an edge, and r s has none because it reverses the edge avoiding u and v, so the acyclic orientations not fixed by s number a multiple of 4. The orientations fixed by s are those that give v the arcs of u, and deleting v is a bijection from them onto the acyclic orientations of the graph without v: a directed cycle through v becomes a closed walk through u. Hence psi(G) and psi(G - v) agree modulo 4. In K_{m,n,p} two vertices of the same part are such twins, and one vertex from each of the other two parts gives an edge avoiding them; removing vertices this way ends at the triangle K_{1,1,1}, whose 8 orientations are 6 transitive ones and 2 cyclic ones. So psi(K_{m,n,p}) is congruent to 6, that is to 2, modulo 4, for all m, n, p at least 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.IsAcyclic`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.IsOrientation`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.acyclicOrientationCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.result`
