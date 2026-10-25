# A nonfactorizable doubled triangle

## Abstract

A doubled triangle with simultaneous exchange of edge copies has no local factorization.

Vertices are indexed by Fin (n + 1). A and B denote the specified actions on vertices and multifacets, respectively. Membership proofs in subtype constructors are implicit; these proofs do not affect values.

**Definition 1.1 (Weighted simplicial complexes).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.WeightedSimplicialComplex}\left(\omega\right)) \Leftrightarrow ((\forall (S: \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)), (\forall (T: \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)), ((S \subseteq T) \Rightarrow (\omega\left(S\right) \mid \omega\left(T\right))))) \land (\forall (i: \operatorname{Fin}\left(n + 1\right)), (\omega\left(\{i\}\right) \ne (0: \mathbb{N}))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.WeightedSimplicialComplex` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

A natural weight is assigned to every vertex subset. Weights divide the weights of larger subsets, and every singleton has nonzero weight. These are the divisibility condition and standing singleton assumption of Definition def:wsc, TeX lines 318–327.

**Definition 1.2 (Distinct copies of each facet).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right): \operatorname{Type}) = \operatorname{Sigma}\left(\lambda (F: \{(S: \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \mid (\operatorname{Maximal}\left(\lambda (T: \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \mapsto (\omega\left(T\right) \ne (0: \mathbb{N})), S\right))\}) \mapsto (\operatorname{Fin}\left(\omega\left(\operatorname{Subtype.val}\left(F\right)\right)\right))\right)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Multifacet` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

A facet is a vertex subset maximal among those of nonzero weight. A multifacet consists of a facet F and an index in Fin (ω F), giving exactly ω F distinct copies. This is the multifacet multiset of Definition def:wsc, TeX lines 327–332, expressed as a dependent sum.

**Definition 1.3 (Forgetting the copy index).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), (\forall (x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.collapse}\left(x\right): \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) = \operatorname{Subtype.val}\left(\operatorname{Sigma.fst}\left(x\right)\right))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.collapse` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

Collapse sends a multifacet to its underlying vertex subset by projecting its facet and then its subset. It is the canonical collapse map of TeX line 332.

**Definition 1.4 (Multifacets incident to a vertex).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), (\forall (i: \operatorname{Fin}\left(n + 1\right)), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Incident}\left(\omega, i\right): \operatorname{Type}) = \{(x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \mid (i \in \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.collapse}\left(x\right))\})))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Incident` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

The local multifacets at i are exactly the multifacets whose underlying facet contains i. This retains each copy separately, as in TeX lines 330–332.

**Definition 1.5 (Compatible vertex and multifacet actions).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), (\forall (G: \operatorname{Type}), ([\operatorname{Group}\left(G\right)], (\forall (A: \operatorname{MulAction}\left(G, \operatorname{Fin}\left(n + 1\right)\right)), (\forall (B: \operatorname{MulAction}\left(G, \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)\right)), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Compatible}\left(\omega, G, A, B\right)) \Leftrightarrow ((\forall (g: G), (\forall (S: \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)), (\omega\left(\operatorname{Finset.image}\left(\lambda (x: \operatorname{Fin}\left(n + 1\right)) \mapsto (A.\operatorname{smul}\left(g, x\right)), S\right)\right) = \omega\left(S\right)))) \land (\forall (g: G), (\forall (x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)), (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.collapse}\left(B.\operatorname{smul}\left(g, x\right)\right) = \operatorname{Finset.image}\left(\lambda (x: \operatorname{Fin}\left(n + 1\right)) \mapsto (A.\operatorname{smul}\left(g, x\right)), \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.collapse}\left(x\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Compatible` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

The vertex action preserves every weight, and collapse intertwines the multifacet action with the induced action on vertex subsets. These are precisely the two requirements in the definition of an action on a weighted simplicial complex, TeX lines 425–435. No finiteness assumption on G is needed here.

**Definition 1.6 (Inverse pullback of local labels).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), (\forall (G: \operatorname{Type}), ([\operatorname{Group}\left(G\right)], (\forall (A: \operatorname{MulAction}\left(G, \operatorname{Fin}\left(n + 1\right)\right)), (\forall (B: \operatorname{MulAction}\left(G, \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)\right)), (\forall (h: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Compatible}\left(\omega, G, A, B\right)), (\forall (\iota: \operatorname{Type}), (\forall (g: G), (\forall (i: \operatorname{Fin}\left(n + 1\right)), (\forall (\beta: (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Incident}\left(\omega, i\right)) \to (\iota)), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.transport}\left(h, g, i, \beta\right): (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Incident}\left(\omega, A.\operatorname{smul}\left(g, i\right)\right)) \to (\iota)) = \lambda (x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Incident}\left(\omega, A.\operatorname{smul}\left(g, i\right)\right)) \mapsto (\beta\left(\langle B.\operatorname{smul}\left(\operatorname{Inv.inv}\left(g\right), \operatorname{Subtype.val}\left(x\right)\right) \rangle\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.transport` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

A local labeling β at i is transported to the labeling at g i that evaluates β on the inverse translate of each multifacet. Collapse compatibility ensures that this inverse translate is incident to i. This is the inverse pullback action on functions and translated subsets of TeX lines 405–413.

**Definition 1.7 (The stabilizer count).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), (\forall (G: \operatorname{Type}), ([\operatorname{Group}\left(G\right)], (\forall (A: \operatorname{MulAction}\left(G, \operatorname{Fin}\left(n + 1\right)\right)), (\forall (B: \operatorname{MulAction}\left(G, \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)\right)), (\forall (\iota: \operatorname{Type}), (\forall (\alpha: (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \to (\iota)), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.K}\left(G, A, B, \alpha\right): \mathbb{N}) = \operatorname{Nat.card}\left(\{(\gamma: (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \to (\iota)) \mid (\forall (i: \operatorname{Fin}\left(n + 1\right)), (\exists (g: G), ((A.\operatorname{smul}\left(g, i\right) = i) \land (\operatorname{Subtype.restrict}\left(\lambda (x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \mapsto (i \in \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.collapse}\left(x\right)), \lambda (x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \mapsto (\gamma\left(B.\operatorname{smul}\left(\operatorname{Inv.inv}\left(g\right), x\right)\right))\right) = \operatorname{Subtype.restrict}\left(\lambda (x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \mapsto (i \in \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.collapse}\left(x\right)), \alpha\right)))))\}\right)))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.K` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

For a labeling α, count all global labelings γ whose restriction at each vertex can be changed into the restriction of α by an element fixing that vertex. The group element may be chosen independently at every vertex. This is K in TeX lines 1519–1521. The definition uses Nat.card for an arbitrary label type ι; the factorization equations below use finite label types.

**Definition 1.8 (Positive equivariant local factorization).**

$$\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), (\forall (G: \operatorname{Type}), ([\operatorname{Group}\left(G\right)], ([\operatorname{Fintype}\left(G\right)], (\forall (A: \operatorname{MulAction}\left(G, \operatorname{Fin}\left(n + 1\right)\right)), (\forall (B: \operatorname{MulAction}\left(G, \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)\right)), (\forall (h: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Compatible}\left(\omega, G, A, B\right)), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Factorizable}\left(\omega, G, A, B, h\right)) \Leftrightarrow (\forall (m: \mathbb{N}), (\exists (C: (i: \operatorname{Fin}\left(n + 1\right)) \to (((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Incident}\left(\omega, i\right)) \to (\operatorname{Fin}\left(m\right))) \to (\mathbb{R}))), ((\forall (i: \operatorname{Fin}\left(n + 1\right)), (\forall (\beta: (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Incident}\left(\omega, i\right)) \to (\operatorname{Fin}\left(m\right))), ((0: \mathbb{R}) < C\left(i, \beta\right)))) \land ((\forall (g: G), (\forall (i: \operatorname{Fin}\left(n + 1\right)), (\forall (\beta: (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Incident}\left(\omega, i\right)) \to (\operatorname{Fin}\left(m\right))), (C\left(A.\operatorname{smul}\left(g, i\right), \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.transport}\left(h, g, i, \beta\right)\right) = C\left(i, \beta\right))))) \land (\forall (\alpha: (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \to (\operatorname{Fin}\left(m\right))), (\prod_{(i: \operatorname{Fin}\left(n + 1\right))} (C\left(i, \operatorname{Subtype.restrict}\left(\lambda (x: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)) \mapsto (i \in \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.collapse}\left(x\right)), \alpha\right)\right)) = \operatorname{Inv.inv}\left((\operatorname{Nat.cast}\left(\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.K}\left(G, A, B, \alpha\right)\right): \mathbb{R})\right)))))))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Factorizable` (`✓ std3`).

*Citation.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

For every natural m, choose a real factor C i β for each vertex and each local labeling by Fin m. Every factor must be positive, transported local labelings must have the same factor, and the product over vertices must equal the reciprocal of K for every global labeling. K is cast from ℕ to ℝ before inversion. Fin m represents every finite label set, including the empty one. The group is finite. These are the equations and inequalities of TeX lines 1515–1522.

**Definition 1.9 (Universal factorizability).**

$$(\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (\omega: (\operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)) \to (\mathbb{N})), ((\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.WeightedSimplicialComplex}\left(\omega\right)) \Rightarrow (\forall (G: \operatorname{Type}), ([\operatorname{Group}\left(G\right)], ([\operatorname{Fintype}\left(G\right)], (\forall (A: \operatorname{MulAction}\left(G, \operatorname{Fin}\left(n + 1\right)\right)), (\forall (B: \operatorname{MulAction}\left(G, \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Multifacet}\left(\omega\right)\right)), (\forall (h: \operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Compatible}\left(\omega, G, A, B\right)), (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.Factorizable}\left(\omega, G, A, B, h\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

Every weighted simplicial complex on Fin (n + 1), with every finite group and every compatible pair of actions, is asserted to be factorizable. Its negation supplies a nonfactorizable structure and hence answers the existence question at TeX lines 1544–1549 affirmatively.

**Theorem 1.10 (The doubled triangle is not factorizable).**

$$\neg (\operatorname{D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.result` (`✓ std3`). ∎

*Resolves.* `Problems/delascuevas-klingler-netzer-2024-nonfactorizable-doubled-triangle` (refuted) by `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"delascuevas-klingler-netzer-2024-nonfactorizable-doubled-triangle","declaration_gid":"D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gemma De las Cuevas; Andreas Klingler; Tim Netzer (2024). *Polynomial decompositions with invariance and positivity inspired by tensors*. DOI: [10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025). URL: <https://arxiv.org/abs/2109.06680v2>.

*Commentary.*

On the vertices 0, 1, 2, give the empty set and singletons weight 1, the three edges weight 2, and the full vertex set weight 0. These weights satisfy divisibility and the singleton condition. The facets are exactly the complements of the single vertices. Index their copies by pairs (e,k) in Fin 3 × Fin 2, where the underlying edge omits e. This indexing is bijective, and a copy is incident to i exactly when i differs from e.

Use MulAction.ofEndHom with the constant identity endomorphism homomorphism to let Multiplicative (ZMod 2) fix every vertex. Its identity fixes every copy, and its other element reverses the Fin 2 index on each edge simultaneously. Reversal is an involution, so these maps define a group action. They preserve each underlying edge, while the vertex action preserves every weight; the two actions are therefore compatible.

For a,b,c in Fin 2, define αₐᵦ𝒸 by labeling copy 0 of every edge with 0 and copy 1 of the edges omitting 0, 1, 2 with a, b, c, respectively. In these coordinates, equality of the local pullbacks means that, at each vertex i, γ agrees with αₐᵦ𝒸 on all copies of edges not omitting i, either directly or after reversing both copy indices. These are the only two possibilities because the group has two elements, each equal to its inverse. The bijection of copies transfers K to the cardinality of this set of binary functions. Enumerating the eight choices of a,b,c and the binary functions gives K(α₀₀₀) = 1 and K(αₐᵦ𝒸) = 2 for all other choices.

For any real local factors C, let Pₐᵦ𝒸 be their product over the three vertices at the restrictions of αₐᵦ𝒸. The restriction at vertex 0 is independent of a, the restriction at vertex 1 is independent of b, and the restriction at vertex 2 is independent of c: each vertex sees only the two edges that contain it. Consequently P₀₀₀ P₀₁₁ P₁₀₁ P₁₁₀ = P₀₀₁ P₀₁₀ P₁₀₀ P₁₁₁. For each vertex, the factors on either side contain each possible pair of the other two binary coordinates exactly once; expanding the products and commuting real factors proves the identity.

If the structure were factorizable, take m = 2 in its defining equations. They give P₀₀₀ = 1 and Pₐᵦ𝒸 = 1/2 for all other choices. Substitution into the parity identity yields 1/8 = 1/16, a contradiction. Thus even the product equations have no solution; positivity and equivariance cannot restore one. Finally, applying universal factorizability to n = 2, these weights, this finite group and these compatible actions would give the impossible factorization. Hence claim is false.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Compatible`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Factorizable`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Incident`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.K`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.Multifacet`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.WeightedSimplicialComplex`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.claim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.collapse`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.result`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.transport`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](../../../S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.md)
