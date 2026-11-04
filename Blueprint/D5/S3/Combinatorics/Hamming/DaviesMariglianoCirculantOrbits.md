# A circulant counterexample to the orbit–eigenvalue conjecture

## Abstract

A graph on thirty vertices has a cyclic symmetry, at least eight orbits of unordered vertex pairs under its full automorphism group, and at most seven distinct real adjacency eigenvalues.

**Definition 1.1 (A cyclic symmetry on all vertices).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{IsCirculant}\left(G\right)) \Leftrightarrow ((0 < n) \land (\exists (s: \operatorname{SimpleGraph}.\operatorname{Iso}\left(G, G\right)), \operatorname{Equiv}.\operatorname{Perm}.\operatorname{IsCycleOn}\left(s.\operatorname{toEquiv}, \operatorname{Set}.\operatorname{univ}\right)))$$

*Formalization.* `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.IsCirculant` (`✓ std3`).

*Citation.* Isobel Davies and Orlando Marigliano (2021). *Coloured Graphical Models and their Symmetries*. URL: <https://arxiv.org/abs/2012.01905v5>.

*Commentary.*

Section 4, page 11: "By definition, these are graphs that have a symmetry which is a cyclic permutation of its vertices." Vertices are Fin n. The positive order and the graph isomorphism G ≃g G express a symmetry on the entire vertex set; IsCycleOn is applied to its underlying permutation and Set.univ.

**Definition 1.2 (Orbits of unordered pairs).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{pairOrbits}\left(G\right) = \operatorname{Set}.\operatorname{range}\left(fun (p: \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{Set}.\operatorname{range}\left(fun (s: \operatorname{SimpleGraph}.\operatorname{Iso}\left(G, G\right)) \mapsto \operatorname{Sym2}.\operatorname{map}\left(s, p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.pairOrbits` (`✓ std3`).

*Citation.* Isobel Davies and Orlando Marigliano (2021). *Coloured Graphical Models and their Symmetries*. URL: <https://arxiv.org/abs/2012.01905v5>.

*Commentary.*

Corollary 3.3, page 7: "In particular, let V * V be the set of unordered pairs of vertices of G and s the number of orbits of the entrywise action of Aut(G) on V * V." The proof specifies that the number of elements in V * V is binomial(n+1,2), so Sym2 retains diagonal pairs. Each inner Set.range uses every graph automorphism. The outer Set.range collects the distinct orbits.

**Definition 1.3 (Distinct real adjacency eigenvalues).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{eigenvalueCount}\left(G\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Module}.\operatorname{End}.\operatorname{Eigenvalues}\left((G.\operatorname{adjMatrix}\left(\mathbb{R}\right)).\operatorname{mulVecLin}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.eigenvalueCount` (`✓ std3`).

*Citation.* Isobel Davies and Orlando Marigliano (2021). *Coloured Graphical Models and their Symmetries*. URL: <https://arxiv.org/abs/2012.01905v5>.

*Commentary.*

Conjecture 4.4, page 11: "If G is an uncoloured circulant graph, then the number of orbits of the action of Aut(G) on the set V*V of unordered pairs of vertices of G coincides with the number of distinct eigenvalues of its adjacency matrix." SimpleGraph.adjMatrix has entries one at adjacent vertices and zero elsewhere. Module.End.Eigenvalues is a set of scalars, and Nat.card counts its subtype without multiplicity. The real adjacency matrix of a simple undirected graph is symmetric. Classical decidability supplies the matrix for arbitrary G.

**Definition 1.4 (Davies–Marigliano Conjecture 4.4).**

$$(claim) \Leftrightarrow (\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{IsCirculant}\left(G\right)) \Rightarrow (\operatorname{Nat}.\operatorname{card}\left(\operatorname{pairOrbits}\left(G\right)\right) = \operatorname{eigenvalueCount}\left(G\right)))$$

*Formalization.* `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.claim` (`✓ std3`).

*Citation.* Isobel Davies and Orlando Marigliano (2021). *Coloured Graphical Models and their Symmetries*. URL: <https://arxiv.org/abs/2012.01905v5>.

*Commentary.*

Conjecture 4.4, page 11 of arXiv:2012.01905v5: "If G is an uncoloured circulant graph, then the number of orbits of the action of Aut(G) on the set V*V of unordered pairs of vertices of G coincides with the number of distinct eigenvalues of its adjacency matrix." The universal quantifiers range over n : ℕ and every simple undirected graph on Fin n. IsCirculant includes positive order. Pair orbits include the diagonal and use the full automorphism group.

**Theorem 1.5 (The universal equality is false).**

$$\neg (\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{IsCirculant}\left(G\right)) \Rightarrow (\operatorname{Nat}.\operatorname{card}\left(\operatorname{pairOrbits}\left(G\right)\right) = \operatorname{eigenvalueCount}\left(G\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.result` (`✓ std3`). ∎

*Resolves.* `Problems/davies-marigliano-2021-circulant-orbit-eigenvalue-conjecture` (refuted) by `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"davies-marigliano-2021-circulant-orbit-eigenvalue-conjecture","declaration_gid":"D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Isobel Davies and Orlando Marigliano (2021). *Coloured Graphical Models and their Symmetries*. URL: <https://arxiv.org/abs/2012.01905v5>.

*Commentary.*

On Fin 30, join two vertices when their residues modulo 2, 3 and 5 disagree in exactly one coordinate. Translation by one is a cyclic graph symmetry. The three edge types have respectively zero, one and three common neighbours. These intrinsic counts distinguish the types under every automorphism; paths using the other two types recover equality of each coordinate. The eight coordinate disagreement patterns therefore give at least eight distinct unordered-pair orbits. An integer circulant certificate shows that the adjacency operator is annihilated by X(X−7)(X−5)(X−4)(X−2)(X+1)(X+3). Applying this identity to an eigenvector places every real eigenvalue in {−3,−1,0,2,4,5,7}. Hence there are at most seven distinct eigenvalues, contradicting the equality. The proof uses only these bounds; exact counts and infinite families are separate assertions.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.IsCirculant`
- Truth anchor: `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.claim`
- Truth anchor: `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.eigenvalueCount`
- Truth anchor: `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.pairOrbits`
- Truth anchor: `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.result`
