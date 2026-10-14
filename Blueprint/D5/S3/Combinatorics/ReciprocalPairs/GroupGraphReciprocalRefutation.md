# Campbell's group-graph reciprocal-pair conjecture

## Abstract

A sign-coupled group on three edges and two four-cliques refutes the reciprocal-pair classification.

**Definition 1.1 (Automorphisms).**

$$\forall V \in Type,\; \forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; \forall g \in \operatorname{Equiv.Perm}\left(V\right),\; \operatorname{IsAut}\left(Gamma, g\right) \Leftrightarrow (\forall u \in V,\; \forall v \in V,\; \operatorname{SimpleGraph.Adj}\left(Gamma, g\left(u\right), g\left(v\right)\right) \Leftrightarrow (\operatorname{SimpleGraph.Adj}\left(Gamma, u, v\right)))$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.IsAut` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

Page 4: "By definition, g is an element of the automorphism group if and only if {i, j} and {g(i), g(j)} are both edges in Γ." The permutation preserves adjacency in both directions.

**Definition 1.2 (Cycle polynomial).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(V\right)\right),\; [\operatorname{Fintype}\left(G\right)] \operatorname{cyclePoly}\left(G\right) = \sum_{g: G} ((\operatorname{Polynomial.X}: \operatorname{Polynomial}\left(\mathbb{Z}\right))^{\operatorname{Fintype.card}\left(\operatorname{Quotient}\left(\operatorname{Equiv.Perm.SameCycle.setoid}\left((\operatorname{val}\left(g\right): \operatorname{Equiv.Perm}\left(V\right))\right)\right)\right)})$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.cyclePoly` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

Page 1: "The cycle polynomial of a finite permutation group G acting on a set Ω of size n is" F_G(x) = Σ_{g∈G} x^{c(g)}, "where c(g) is the number of cycles (including fixed points) of g on Ω." SameCycle identifies vertices in a common permutation cycle, including each fixed vertex as a singleton. The coefficients are integers.

**Definition 1.3 (Fixed proper colourings).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; \forall g \in \operatorname{Equiv.Perm}\left(V\right),\; \forall c \in \mathbb{N},\; \operatorname{fixedColourings}\left(Gamma, g, c\right) = \operatorname{Finset.filter}\left(\lambda (f: V \to \operatorname{Fin}\left(c\right)) \mapsto (\forall u \in V,\; \forall v \in V,\; (\operatorname{SimpleGraph.Adj}\left(Gamma, u, v\right)) \Rightarrow (f\left(u\right) \ne f\left(v\right))) \land (\forall v \in V,\; f\left(g\left(v\right)\right) = f\left(v\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(V \to \operatorname{Fin}\left(c\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.fixedColourings` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

Page 1: "A proper colouring of a graph is a map from the vertex set to the set of colourings such that no two adjacent vertices have the same colour." Page 1: "The chromatic polynomial PΓ/g(x) is the polynomial which counts proper colourings of Γ fixed by g." Colours are Fin c; each map is counted once, with adjacent vertices differently coloured and f(g(v)) = f(v).

**Definition 1.4 (Reciprocal pairs).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(V\right)\right),\; [\operatorname{Fintype}\left(G\right)] \operatorname{IsReciprocal}\left(Gamma, G\right) \Leftrightarrow (\forall c \in \mathbb{N},\; (0 < c) \Rightarrow ((\sum_{g: G} (\operatorname{Finset.card}\left(\operatorname{fixedColourings}\left(Gamma, (\operatorname{val}\left(g\right): \operatorname{Equiv.Perm}\left(V\right)), c\right)\right)): \mathbb{Z}) = (-1: \mathbb{Z})^{\operatorname{Fintype.card}\left(V\right)} \cdot \operatorname{Polynomial.eval}\left(-(c: \mathbb{Z}), \operatorname{cyclePoly}\left(G\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.IsReciprocal` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

Page 2: "We call a group-graph pair (Γ, G) a reciprocal pair if the relation" PΓ,G(x) = (−1)^n F_G(−x) "holds for a simple graph Γ with n vertices and where G is an automorphism group of Γ." The equation is evaluated at every positive natural number c. Equality at all these integers is equality of the corresponding polynomials.

**Definition 1.5 (A sufficient obstruction to irreducibility).**

$$\forall V \in Type,\; \forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(V\right)\right),\; \operatorname{Reducible}\left(Gamma, G\right) \Leftrightarrow (\exists m \in \mathbb{N},\; (2 \le m) \land (\exists part \in V \to \operatorname{Fin}\left(m\right),\; (\operatorname{Function.Surjective}\left(part\right)) \land ((\forall u \in V,\; \forall v \in V,\; (\operatorname{SimpleGraph.Adj}\left(Gamma, u, v\right)) \Rightarrow (part\left(u\right) = part\left(v\right))) \land ((\exists Gi \in \operatorname{Fin}\left(m\right) \to \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(V\right)\right),\; (\forall i \in \operatorname{Fin}\left(m\right),\; Gi\left(i\right) \le G) \land ((\forall i \in \operatorname{Fin}\left(m\right),\; \forall g \in \operatorname{Equiv.Perm}\left(V\right),\; (g \in Gi\left(i\right)) \Rightarrow (\forall v \in V,\; (part\left(v\right) \ne i) \Rightarrow (g\left(v\right) = v))) \land (\operatorname{Subgroup.closure}\left(\operatorname{Set.iUnion}\left(\lambda (i: \operatorname{Fin}\left(m\right)) \mapsto (Gi\left(i\right): \operatorname{Set}\left(\operatorname{Equiv.Perm}\left(V\right)\right))\right)\right) = G))) \lor (\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(\operatorname{SimpleGraph.induce}\left(\{v: V \mid part\left(v\right) = i\}, Gamma\right), \operatorname{SimpleGraph.induce}\left(\{v: V \mid part\left(v\right) = j\}, Gamma\right)\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.Reducible` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

Page 3: "A reciprocal pair (Γ, G) is irreducible is there is no non-trivial decomposition Γ = Γ1 ∪ Γ2 ∪ ... ∪ Γn and subgroups Gi ≤ G with Gi ≤ Aut(Γi) such that either" "1. G = G1 × ... × Gn with each (Γi, Gi) a reciprocal pair," "2. Gi ≅ Gj and Γi ≅ Γj for all i ≠ j and G = G0 ≀ H for some H ≤ Sn and G0 ≅ Gi for all i." The displayed predicate allows more decompositions: the first branch requires only generation by subgroups fixing other parts; the second requires only isomorphism of the induced part graphs. Surjectivity and m ≥ 2 make the parts nonempty and the decomposition nontrivial.

**Definition 1.6 (Irreducibility).**

$$\forall V \in Type,\; \forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(V\right)\right),\; \operatorname{IsIrreducible}\left(Gamma, G\right) \Leftrightarrow (\neg (\operatorname{Reducible}\left(Gamma, G\right)))$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.IsIrreducible` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

No decomposition satisfies either of the two conditions in Reducible. Since those conditions include every decomposition in the definition on page 3, this predicate implies the source's irreducibility.

**Definition 1.7 (The listed graph classes).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(V\right)\right),\; \operatorname{Listed}\left(Gamma, G\right) \Leftrightarrow ((\forall u \in V,\; \forall v \in V,\; \neg (\operatorname{SimpleGraph.Adj}\left(Gamma, u, v\right))) \lor ((\forall u \in V,\; \forall v \in V,\; (u \ne v) \Rightarrow (\operatorname{SimpleGraph.Adj}\left(Gamma, u, v\right))) \lor ((\operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(Gamma, \operatorname{SimpleGraph.cycleGraph}\left(4\right)\right)\right)) \lor (\exists k \in \mathbb{N},\; (1 \le k) \land ((k < \operatorname{Fintype.card}\left(V\right)) \land (\exists K \in \operatorname{Finset}\left(V\right),\; (\operatorname{Finset.card}\left(K\right) = k) \land (\forall u \in V,\; \forall v \in V,\; \operatorname{SimpleGraph.Adj}\left(Gamma, u, v\right) \Leftrightarrow ((u \ne v) \land ((u \in K) \lor (v \in K))))))))))$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.Listed` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

Page 3: "1. (Γ, G) is one of the two trivial cases: (a) Γ is a null graph and G is any group with no odd permutations, (b) Γ is the complete graph with n vertices and G = Sn. 2. Γ is a 4-cycle and G ≅ Aut(Γ). 3. Γ is a k-star and G is defined in Theorem 1." The predicate drops the group restrictions and retains these four graph conditions. A k-star has a nonempty proper centre K; distinct vertices are adjacent exactly when at least one lies in K.

**Definition 1.8 (The conjecture).**

$$\operatorname{claim} \Leftrightarrow (\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall Gamma \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(Gamma\right)\right)] \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(V\right)\right),\; [\operatorname{Fintype}\left(G\right)] (\forall g \in \operatorname{Equiv.Perm}\left(V\right),\; (g \in G) \Rightarrow (\operatorname{IsAut}\left(Gamma, g\right))) \Rightarrow ((\operatorname{IsReciprocal}\left(Gamma, G\right)) \Rightarrow ((\operatorname{IsIrreducible}\left(Gamma, G\right)) \Rightarrow (\operatorname{Listed}\left(Gamma, G\right)))))$$

*Formalization.* `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.claim` (`✓ std3`).

*Citation.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Commentary.*

Conjecture, page 3 (verbatim): "Conjecture: Let (Γ, G) be an irreducible reciprocal pair. Then one of the following hold: 1. (Γ, G) is one of the two trivial cases: (a) Γ is a null graph and G is any group with no odd permutations, (b) Γ is the complete graph with n vertices and G = Sn. 2. Γ is a 4-cycle and G ≅ Aut(Γ). 3. Γ is a k-star and G is defined in Theorem 1." V is a finite vertex type, Gamma denotes Γ, and G is a finite subgroup of Equiv.Perm V. Automorphisms, positive-integer evaluations, irreducibility and the listed classes have exactly the meanings displayed above. The broader decomposition test and broader listed conclusion make claim a consequence of the source conjecture.

**Theorem 1.9 (Refutation).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/campbell-2020-group-graph-reciprocal-pairs` (refuted) by `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"campbell-2020-group-graph-reciprocal-pairs","declaration_gid":"D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kirsty Campbell (2020). *Group-Graph Reciprocal Pairs*. DOI: [10.48550/arXiv.2005.13566](https://doi.org/10.48550/arXiv.2005.13566). URL: <https://arxiv.org/abs/2005.13566>.

*Acknowledgement.* Peter J. Cameron, Jason Semeraro (2018). *The cycle polynomial of a permutation group*. DOI: [10.37236/7299](https://doi.org/10.37236/7299). URL: <https://arxiv.org/abs/1701.06954>.

*Commentary.*

The graph 3K₂ ⊔ 2K₄ has fourteen vertices. The group permits all internal clique permutations, with S₃ acting on the three edges naturally and on the two four-cliques through its sign. It is reciprocal: nonproper colourings cancel under an edge transposition, while every permutation fixing a proper colouring has sign +1. Its two clique layers cannot generate the whole coupled group from subgroups supported on separate parts. Pairwise isomorphic parts would have equal even cardinalities, which is incompatible with fourteen vertices and between two and five parts. An edge and a nonedge exclude the two trivial graph classes, cardinality excludes the four-cycle, and the absence of a universal vertex excludes every k-star. The general cycle-polynomial and reciprocity background is Cameron–Semeraro (2018).

## References

- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.IsAut`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.IsIrreducible`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.IsReciprocal`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.Listed`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.Reducible`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.cyclePoly`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.fixedColourings`
- Truth anchor: `D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.result`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIBounds](../../FiniteGroups/NikolovSegal/Equation47TypeIIBounds.md)
