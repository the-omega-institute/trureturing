# A loopless counterexample to Wang–Qin–Xia Conjecture 1.3

## Abstract

A stable loopless family has nontrivially unstable pairs with the four-vertex path.

**Definition 1.1 (Distinct open neighborhoods).**

$$\forall (V: Type), \forall (G: \operatorname{SimpleGraph}\left(V\right)), \operatorname{TwinFree}\left(G\right) = \operatorname{Function}.\operatorname{Injective}\left(\operatorname{SimpleGraph}.\operatorname{neighborSet}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.TwinFree` (`✓ std3`).

*Citation.* Xiaomeng Wang, Yan-Li Qin, Binzhou Xia (2025). *The existence of unexpected automorphisms in direct product graphs*. DOI: [10.48550/arXiv.2509.26170](https://doi.org/10.48550/arXiv.2509.26170). URL: <https://arxiv.org/abs/2509.26170v2>.

*Commentary.*

Page 1: “A graph is called twin-free if no two vertices have the same neighborhood in the graph.” The variable G is a loopless graph on V; injectivity refers to its full open-neighborhood map.

**Definition 1.2 (No nontrivial common direct factor).**

$$\forall (V: Type), \forall (W: Type), \forall (G: \operatorname{SimpleGraph}\left(V\right)), \forall (H: \operatorname{SimpleGraph}\left(W\right)), \operatorname{Coprime}\left(G, H\right) = \left(\neg (\exists (d: Nat), \exists (a: Nat), \exists (b: Nat), \exists (F: \operatorname{LoopGraph}\left(d\right)), \exists (G': \operatorname{LoopGraph}\left(a\right)), \exists (H': \operatorname{LoopGraph}\left(b\right)), (1 < d) \land ((\operatorname{Nonempty}\left(\operatorname{RelIso}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right), (fun (x: \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(d\right)\right)) \mapsto fun (y: \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(d\right)\right)) \mapsto ((\operatorname{LoopGraph}.\operatorname{edge}\left(G', \operatorname{Prod}.\operatorname{fst}\left(x\right), \operatorname{Prod}.\operatorname{fst}\left(y\right)\right)) \land (\operatorname{LoopGraph}.\operatorname{edge}\left(F, \operatorname{Prod}.\operatorname{snd}\left(x\right), \operatorname{Prod}.\operatorname{snd}\left(y\right)\right))))\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{RelIso}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(H\right), (fun (x: \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(d\right)\right)) \mapsto fun (y: \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(d\right)\right)) \mapsto ((\operatorname{LoopGraph}.\operatorname{edge}\left(H', \operatorname{Prod}.\operatorname{fst}\left(x\right), \operatorname{Prod}.\operatorname{fst}\left(y\right)\right)) \land (\operatorname{LoopGraph}.\operatorname{edge}\left(F, \operatorname{Prod}.\operatorname{snd}\left(x\right), \operatorname{Prod}.\operatorname{snd}\left(y\right)\right))))\right)\right))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.Coprime` (`✓ std3`).

*Citation.* Xiaomeng Wang, Yan-Li Qin, Binzhou Xia (2025). *The existence of unexpected automorphisms in direct product graphs*. DOI: [10.48550/arXiv.2509.26170](https://doi.org/10.48550/arXiv.2509.26170). URL: <https://arxiv.org/abs/2509.26170v2>.

*Commentary.*

Page 1: “We say that graphs Γ and Σ are coprime (with respect to the direct product) if there exists no graph Δ of order greater than 1 such that Γ ≅ Γ′×Δ and Σ ≅ Σ′×Δ for some graphs Γ′ and Σ′.” The graphs G and H represent Γ and Σ. The common factor F and the cofactors G′ and H′ are arbitrary finite symmetric relations, including diagonal edges. Their carriers Fin d, Fin a and Fin b cover every finite isomorphism class. RelIso preserves and reflects adjacency.

**Definition 1.3 (Componentwise automorphisms).**

$$\forall (V: Type), \forall (W: Type), \forall (G: \operatorname{SimpleGraph}\left(V\right)), \forall (H: \operatorname{SimpleGraph}\left(W\right)), \operatorname{StablePair}\left(G, H\right) = (\forall (f: \operatorname{SimpleGraph}.\operatorname{Iso}\left(\operatorname{dirProd}\left(G, H\right), \operatorname{dirProd}\left(G, H\right)\right)), \exists (\alpha: \operatorname{SimpleGraph}.\operatorname{Iso}\left(G, G\right)), \exists (\beta: \operatorname{SimpleGraph}.\operatorname{Iso}\left(H, H\right)), \forall (p: \operatorname{Prod}\left(V, W\right)), \operatorname{f}\left(p\right) = (\alpha\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right), \beta\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.StablePair` (`✓ std3`).

*Citation.* Xiaomeng Wang, Yan-Li Qin, Binzhou Xia (2025). *The existence of unexpected automorphisms in direct product graphs*. DOI: [10.48550/arXiv.2509.26170](https://doi.org/10.48550/arXiv.2509.26170). URL: <https://arxiv.org/abs/2509.26170v2>.

*Commentary.*

Page 1: “In other words, (Γ,Σ) is stable if and only if (1) is an equality.” Equation (1) is Aut(Γ)×Aut(Σ) ≤ Aut(Γ×Σ), with componentwise action. The formula says that every automorphism f of dirProd G H is induced by graph automorphisms α of G and β of H. It quantifies over all vertices of the product.

**Definition 1.4 (Stability of a single graph).**

$$\forall (V: Type), \forall (G: \operatorname{SimpleGraph}\left(V\right)), \operatorname{StableGraph}\left(G\right) = \operatorname{StablePair}\left(G, (\operatorname{Top}.\operatorname{top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(2\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.StableGraph` (`✓ std3`).

*Citation.* Xiaomeng Wang, Yan-Li Qin, Binzhou Xia (2025). *The existence of unexpected automorphisms in direct product graphs*. DOI: [10.48550/arXiv.2509.26170](https://doi.org/10.48550/arXiv.2509.26170). URL: <https://arxiv.org/abs/2509.26170v2>.

*Commentary.*

Page 1: “Indeed, a graph Γ is stable in the sense of [7] if and only if the pair (Γ,K₂) is stable.” The complete loopless graph on Fin 2 represents K₂.

**Definition 1.5 (The hypotheses on a graph pair).**

$$\forall (V: Type), \forall (W: Type), \forall (G: \operatorname{SimpleGraph}\left(V\right)), \forall (H: \operatorname{SimpleGraph}\left(W\right)), \operatorname{Nontrivial}\left(G, H\right) = \left((\operatorname{Coprime}\left(G, H\right)) \land ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \land ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(H\right)) \land ((\operatorname{TwinFree}\left(G\right)) \land ((\operatorname{TwinFree}\left(H\right)) \land (((\operatorname{SimpleGraph}.\operatorname{IsBipartite}\left(G\right)) \land (\neg \operatorname{SimpleGraph}.\operatorname{IsBipartite}\left(H\right))) \lor ((\neg \operatorname{SimpleGraph}.\operatorname{IsBipartite}\left(G\right)) \land (\operatorname{SimpleGraph}.\operatorname{IsBipartite}\left(H\right))))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.Nontrivial` (`✓ std3`).

*Citation.* Xiaomeng Wang, Yan-Li Qin, Binzhou Xia (2025). *The existence of unexpected automorphisms in direct product graphs*. DOI: [10.48550/arXiv.2509.26170](https://doi.org/10.48550/arXiv.2509.26170). URL: <https://arxiv.org/abs/2509.26170v2>.

*Commentary.*

Definition 1.1, page 1: “A graph pair (Γ,Σ) is nontrivial if Γ and Σ are coprime connected twin-free graphs and exactly one of them is bipartite.” Connectedness, injectivity of the open-neighborhood maps, and both alternatives for the bipartite factor are retained.

**Definition 1.6 (Conjecture 1.3).**

$$(claim: Prop) = (\forall (V: Type), \forall (W: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \forall (Gamma: \operatorname{SimpleGraph}\left(V\right)), \forall (Sigma: \operatorname{SimpleGraph}\left(W\right)), (\operatorname{Nontrivial}\left(Gamma, Sigma\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{IsBipartite}\left(Sigma\right)) \Rightarrow ((\operatorname{StablePair}\left(Gamma, Sigma\right)) \Leftrightarrow (\operatorname{StableGraph}\left(Gamma\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.claim` (`✓ std3`).

*Citation.* Xiaomeng Wang, Yan-Li Qin, Binzhou Xia (2025). *The existence of unexpected automorphisms in direct product graphs*. DOI: [10.48550/arXiv.2509.26170](https://doi.org/10.48550/arXiv.2509.26170). URL: <https://arxiv.org/abs/2509.26170v2>.

*Commentary.*

Conjecture 1.3, page 2: “Let (Γ,Σ) be a nontrivial graph pair without loops, where Σ is bipartite. Then (Γ,Σ) is stable if and only if Γ is stable.” V and W are finite vertex types, Gamma and Sigma are SimpleGraph values, and Sigma.IsBipartite is a separate hypothesis. The SimpleGraph carriers enforce looplessness. The implication retains the whole predicate Nontrivial, even though one of its bipartiteness alternatives follows from the separate hypothesis.

**Theorem 1.7 (The loopless conjecture is false).**

$$\neg (\forall (V: Type), \forall (W: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \forall (Gamma: \operatorname{SimpleGraph}\left(V\right)), \forall (Sigma: \operatorname{SimpleGraph}\left(W\right)), (\operatorname{Nontrivial}\left(Gamma, Sigma\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{IsBipartite}\left(Sigma\right)) \Rightarrow ((\operatorname{StablePair}\left(Gamma, Sigma\right)) \Leftrightarrow (\operatorname{StableGraph}\left(Gamma\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/wqx-loopless-stability-refutation` (refuted) by `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wqx-loopless-stability-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xiaomeng Wang, Yan-Li Qin, Binzhou Xia (2025). *The existence of unexpected automorphisms in direct product graphs*. DOI: [10.48550/arXiv.2509.26170](https://doi.org/10.48550/arXiv.2509.26170). URL: <https://arxiv.org/abs/2509.26170v2>.

*Commentary.*

For every m ≥ 3, take vertices (t,a,b) in Fin m × Bool × Bool and put R(a,b) precisely when a=true or b=true. Two vertices (t,a,b) and (u,c,d) are adjacent precisely when t≠u, R(a,d), and R(c,b). This is loopless. The second graph has vertices (s,i) in Bool × Bool and adjacency s≠r together with R(i,j); it is the four-vertex path. Neighborhood inclusion gives one four-element diamond at each index. Preservation of these diamonds under a two-fold automorphism, and a third index, force its two permutations to agree. This makes the first graph stable. Every independent set in it has at most m+2 vertices, excluding a half-size independent slice from a two-vertex common factor; a four-vertex common factor would force bipartiteness. The graph pair is connected, twin-free, coprime even when factors have loops, and has exactly one bipartite factor. In the product, the involution sends ((t,a,b),(false,i)) to ((t,a,i),(false,b)) and ((t,a,b),(true,j)) to ((t,j,b),(true,a)). It preserves adjacency and acts noncomponentwise. The case m=3 contradicts the universal equivalence.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.Coprime`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.Nontrivial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.StableGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.StablePair`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.TwinFree`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.result`
- Dependency: [D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization](../../ConstraintRelations/RationalPositiveRealization.md)
- Dependency: [D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap](../../../StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.md)
