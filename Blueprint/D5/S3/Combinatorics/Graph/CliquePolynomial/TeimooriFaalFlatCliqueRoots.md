# A flat graph whose clique polynomial has a nonreal root

## Abstract

Four complete four-vertex graphs joined in a ring give a twelve-vertex counterexample to Conjecture 1 of On Clique Roots of Flat Graphs.

**Definition 1.1 (The clique polynomial).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(G.Adj\right)] \operatorname{cliquePoly}\left(G\right) = \sum_{j \in \operatorname{Finset.range}\left((\operatorname{Fintype.card}\left(V\right) + 1)\right)} \operatorname{Polynomial.C}\left((\operatorname{Finset.card}\left(\operatorname{SimpleGraph.cliqueFinset}\left(G, j\right)\right) : \mathbb{Z})\right) \cdot \operatorname{Polynomial.X}^{j}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.cliquePoly` (`✓ std3`).

*Citation.* H. Teimoori Faal (2021). *On Clique Roots of Flat Graphs*. DOI: [10.48550/arXiv.2112.09721](https://doi.org/10.48550/arXiv.2112.09721). URL: <https://arxiv.org/abs/2112.09721v1>.

*Commentary.*

Page 1: "For a given graph G, a complete subgraph of G with i-vertices (i ≥ 1) is called an i-clique of G." Equation (1) defines C(G, x) = ∑_{k=0}^{ω(G)} c_k(G)x^k, "where by convention c₀(G) is taken to be 1 for any simple graph G." Here c_k(G) counts Mathlib's SimpleGraph.cliqueFinset k. The Lean sum includes the empty clique and all sizes from 0 through Fintype.card V; terms beyond the clique number are zero. Coefficients are integers; Polynomial.C embeds each count as a constant polynomial, and Polynomial.X is the polynomial variable.

**Definition 1.2 (Flatness).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(G.Adj\right)] \operatorname{IsFlat}\left(G\right) \Leftrightarrow (\forall (u : V), \forall (v : V), (\operatorname{SimpleGraph.Adj}\left(G, u, v\right)) \Rightarrow (\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((\lambda w \mapsto ((\operatorname{SimpleGraph.Adj}\left(G, u, w\right)) \land (\operatorname{SimpleGraph.Adj}\left(G, v, w\right)))), \operatorname{Finset.univ}\right)\right) \le 2))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.IsFlat` (`✓ std3`).

*Citation.* H. Teimoori Faal (2021). *On Clique Roots of Flat Graphs*. DOI: [10.48550/arXiv.2112.09721](https://doi.org/10.48550/arXiv.2112.09721). URL: <https://arxiv.org/abs/2112.09721v1>.

*Commentary.*

Definition 2.2, page 4: "A graph G is called flat if every edge of G belongs to at most two triangles of G." For an edge uv, the third vertex of each triangle is a common neighbour of u and v. The filtered finite set counts these third vertices.

**Definition 1.3 (Absence of isolated triangles).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{NoIsolatedTriangle}\left(G\right) \Leftrightarrow (\forall (u : V), \forall (v : V), \forall (w : V), (\operatorname{SimpleGraph.Adj}\left(G, u, v\right)) \Rightarrow ((\operatorname{SimpleGraph.Adj}\left(G, v, w\right)) \Rightarrow ((\operatorname{SimpleGraph.Adj}\left(G, u, w\right)) \Rightarrow (\exists (x : V), (\operatorname{SimpleGraph.Adj}\left(G, u, x\right)) \land ((\operatorname{SimpleGraph.Adj}\left(G, v, x\right)) \land (\operatorname{SimpleGraph.Adj}\left(G, w, x\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.NoIsolatedTriangle` (`✓ std3`).

*Citation.* H. Teimoori Faal (2021). *On Clique Roots of Flat Graphs*. DOI: [10.48550/arXiv.2112.09721](https://doi.org/10.48550/arXiv.2112.09721). URL: <https://arxiv.org/abs/2112.09721v1>.

*Commentary.*

Definition 4.1, page 6: "For a triangle δ = {u, v, w} ⊂ V(G), the value of δ in G denoted by val_G(δ) is defined by val_G(δ) = N_G(u) ∩ N_G(v) ∩ N_G(w). Moreover, a triangle is called isolated if its triangle value is zero." Thus every triangle must have a vertex adjacent to all three of its vertices. Adjacency is irreflexive, so this common neighbour differs from each triangle vertex.

**Definition 1.4 (Teimoori Faal's Conjecture 1).**

$$claim \Leftrightarrow (\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(G.Adj\right)] (3 \le \operatorname{Fintype.card}\left(V\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected}\left(G\right)) \Rightarrow ((\operatorname{SimpleGraph.CliqueFree}\left(G, 5\right)) \Rightarrow ((\operatorname{IsFlat}\left(G\right)) \Rightarrow ((\operatorname{NoIsolatedTriangle}\left(G\right)) \Rightarrow ((\forall (z : \mathbb{C}), (\operatorname{Polynomial.aeval}\left(z, \operatorname{cliquePoly}\left(G\right)\right) = 0) \Rightarrow (\operatorname{Complex.im}\left(z\right) = 0)) \land (\operatorname{Polynomial.rootMultiplicity}\left((-1), \operatorname{cliquePoly}\left(G\right)\right) = 2)))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.claim` (`✓ std3`).

*Citation.* H. Teimoori Faal (2021). *On Clique Roots of Flat Graphs*. DOI: [10.48550/arXiv.2112.09721](https://doi.org/10.48550/arXiv.2112.09721). URL: <https://arxiv.org/abs/2112.09721v1>.

*Commentary.*

Conjecture 1, page 6: "The class of 2-connected K₅-free flat graphs without isolated triangles has only clique roots. In particular, this class has always the clique root r = −1 of multiplicity 2." The source, page 4, says "we will call a real root of C(G, x) a clique root of G." Accordingly, all complex zeros must have imaginary part zero. The second conjunct says that −1 has root multiplicity exactly two. The vertex type is finite, adjacency is decidable, and there are at least three vertices. Biconnected means connected and connected after deletion of any one vertex; it is the existing D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected predicate. K₅-freeness is SimpleGraph.CliqueFree 5.

**Theorem 1.5 (A twelve-vertex refutation).**

$$\neg (\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(G.Adj\right)] (3 \le \operatorname{Fintype.card}\left(V\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected}\left(G\right)) \Rightarrow ((\operatorname{SimpleGraph.CliqueFree}\left(G, 5\right)) \Rightarrow ((\operatorname{IsFlat}\left(G\right)) \Rightarrow ((\operatorname{NoIsolatedTriangle}\left(G\right)) \Rightarrow ((\forall (z : \mathbb{C}), (\operatorname{Polynomial.aeval}\left(z, \operatorname{cliquePoly}\left(G\right)\right) = 0) \Rightarrow (\operatorname{Complex.im}\left(z\right) = 0)) \land (\operatorname{Polynomial.rootMultiplicity}\left((-1), \operatorname{cliquePoly}\left(G\right)\right) = 2)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.result` (`✓ std3`). ∎

*Resolves.* `Problems/teimoori-faal-2021-flat-graph-clique-roots-conjecture-1` (refuted) by `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"teimoori-faal-2021-flat-graph-clique-roots-conjecture-1","declaration_gid":"D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. Teimoori Faal (2021). *On Clique Roots of Flat Graphs*. DOI: [10.48550/arXiv.2112.09721](https://doi.org/10.48550/arXiv.2112.09721). URL: <https://arxiv.org/abs/2112.09721v1>.

*Commentary.*

Take the four complete blocks {0,1,4,5}, {1,2,6,7}, {2,3,8,9}, and {3,0,10,11}, with no other edges. A Hamiltonian cycle remains a spanning path after deleting any vertex. Finite clique enumeration verifies K₅-freeness, flatness and the absence of isolated triangles, and gives the clique counts 1,12,24,16,4, followed by zeros. Hence the clique polynomial is p = 1+12X+24X²+16X³+4X⁴ = 4(1+X)⁴−4X−3. Its derivative is 16(1+X)³−4, with at most one real root and no repeated real roots. The root-count inequality for a polynomial and its derivative precludes splitting of p over ℝ. Splitting over ℂ then supplies a nonreal complex zero, contradicting the first conjunct of the conjecture.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.IsFlat`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.NoIsolatedTriangle`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.cliquePoly`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.result`
- Dependency: [D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation](../../../StatisticalMechanics/DimerVirialFourthDifferenceRefutation.md)
