# Quantum twins and neighbourhood separation

## Abstract

Adjacency determines algebra homomorphisms for finite twin-free graphs.

For a finite vertex type V, the algebra V → ℂ has pointwise operations. The graph adjacency operator sends a point indicator to its neighbourhood indicator. Two vertices are ordinary twins when all their adjacency entries agree. The homomorphism target B may be noncommutative and has no finite dimension requirement. Displayed square brackets are anonymous Lean instance arguments. In the graph structure expression, the proof fields symm and loopless are suppressed; they assert symmetry and irreflexivity of the displayed adjacency relation.

**Definition 1.1 (The adjacency operator).**

$$\forall (V: \operatorname{Type}), ([\operatorname{Fintype}\left(V\right)] \forall (G: \operatorname{SimpleGraph}\left(V\right)), ((\operatorname{adjacencyOperator}\left(G\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), V \to \mathbb{C}, V \to \mathbb{C}\right)) = \operatorname{Matrix.toLin}'\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, G\right)\right)))$$

*Formalization.* `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.adjacencyOperator` (`✓ std3`).

*Citation.* Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan (2025). *Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings*. DOI: [10.48550/arXiv.2502.10521](https://doi.org/10.48550/arXiv.2502.10521). URL: <https://arxiv.org/abs/2502.10521v2>.

*Commentary.*

For the classical graph, C(G) = V → ℂ and A_G acts by summing over adjacent vertices. Here adjacencyOperator G is exactly Matrix.toLin' of SimpleGraph.adjMatrix ℂ G, with its usual row action on column functions. This is the classical specialization of the adjacency operator used in Section 3 of the source.

**Definition 1.2 (Distinct homomorphisms agreeing after adjacency).**

$$\forall (V: \operatorname{Type}), ([\operatorname{Fintype}\left(V\right)] \forall (G: \operatorname{SimpleGraph}\left(V\right)), (\forall (B: \operatorname{Type}), ([\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)] (\operatorname{HasTwinsIn}\left(G, B\right): \operatorname{Prop}) = \exists (\rho_{1}: \operatorname{AlgHom}\left(\mathbb{C}, V \to \mathbb{C}, B\right)), (\exists (\rho_{2}: \operatorname{AlgHom}\left(\mathbb{C}, V \to \mathbb{C}, B\right)), ((\rho_{1} \ne \rho_{2}) \land (\forall (f: V \to \mathbb{C}), (\left(\rho_{1}\right)\left(\operatorname{adjacencyOperator}\left(G, f\right)\right) = \left(\rho_{2}\right)\left(\operatorname{adjacencyOperator}\left(G, f\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.HasTwinsIn` (`✓ std3`).

*Citation.* Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan (2025). *Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings*. DOI: [10.48550/arXiv.2502.10521](https://doi.org/10.48550/arXiv.2502.10521). URL: <https://arxiv.org/abs/2502.10521v2>.

*Commentary.*

Definition 3.8, p. 10: “Let G = (V_G, ψ_G, A_G) be a quantum graph and H be a compact quantum group. We say that G has H-twin vertices, or simply H-twins, if there exists a pair of different actions of H on G ρ₁, ρ₂ : C(G) → C(G) ⊗ C(H) such that ρ₁ ∘ A_G = ρ₂ ∘ A_G. (4) We say that G has quantum twin vertices if there exists a quantum group H such that G has H-twins.” HasTwinsIn retains distinctness and equality after adjacency while allowing all unital complex algebra homomorphisms into an arbitrary complex algebra B. It does not assert the existence of quantum group actions.

**Definition 1.3 (The prism on the complete graph with five vertices).**

$$(\operatorname{prism}: \operatorname{SimpleGraph}\left((\operatorname{Fin}\left(2\right)) \times (\operatorname{Fin}\left(5\right))\right)) = \operatorname{SimpleGraph.boxProd}\left(\operatorname{SimpleGraph.completeGraph}\left(\operatorname{Fin}\left(2\right)\right), \operatorname{SimpleGraph.completeGraph}\left(\operatorname{Fin}\left(5\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.prism` (`✓ std3`).

*Citation.* Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan (2025). *Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings*. DOI: [10.48550/arXiv.2502.10521](https://doi.org/10.48550/arXiv.2502.10521). URL: <https://arxiv.org/abs/2502.10521v2>.

*Commentary.*

The source, p. 13, calls K₂ □ K₅ “the so-called prism having a basis in K₅”. The vertices are pairs in Fin 2 × Fin 5, and SimpleGraph.boxProd is the Cartesian graph product.

**Definition 1.4 (The Cartesian product of two cycles).**

$$(\operatorname{cycleProduct}: \operatorname{SimpleGraph}\left((\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(3\right))\right)) = \operatorname{SimpleGraph.boxProd}\left(\operatorname{SimpleGraph.cycleGraph}\left(4\right), \operatorname{SimpleGraph.cycleGraph}\left(3\right)\right)$$

*Formalization.* `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.cycleProduct` (`✓ std3`).

*Citation.* Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan (2025). *Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings*. DOI: [10.48550/arXiv.2502.10521](https://doi.org/10.48550/arXiv.2502.10521). URL: <https://arxiv.org/abs/2502.10521v2>.

*Commentary.*

The second graph on p. 13 is C₄ □ C₃. Its vertices are pairs in Fin 4 × Fin 3, with each cycle and their Cartesian product supplied by SimpleGraph.

**Definition 1.5 (The negative answer in a larger class of homomorphisms).**

$$(\operatorname{claim}: \operatorname{Prop}) = \forall (B: \operatorname{Type}), ([\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)] (\neg (\operatorname{HasTwinsIn}\left(\operatorname{prism}, B\right))) \land ((\neg (\operatorname{HasTwinsIn}\left(\operatorname{cycleProduct}, B\right))) \land (\neg (\operatorname{HasTwinsIn}\left((\{\operatorname{Adj} := \lambda (u: \operatorname{Fin}\left(4\right) \to \operatorname{Bool}) \mapsto (\lambda (v: \operatorname{Fin}\left(4\right) \to \operatorname{Bool}) \mapsto (\operatorname{hammingDist}\left(u, v\right) = 1)), \operatorname{symm} := ..., \operatorname{loopless} := ...\}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(4\right) \to \operatorname{Bool}\right)), B\right)))))$$

*Formalization.* `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.claim` (`✓ std3`).

*Citation.* Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan (2025). *Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings*. DOI: [10.48550/arXiv.2502.10521](https://doi.org/10.48550/arXiv.2502.10521). URL: <https://arxiv.org/abs/2502.10521v2>.

*Commentary.*

Question 3.17, p. 13: “Do the above-mentioned graphs possess quantum twin vertices?” The graphs are K₂ □ K₅, C₄ □ C₃ and the tesseract. The last has vertex type Fin 4 → Bool and adjacency hammingDist u v = 1. The formula asserts, for every complex target algebra, the absence of two distinct homomorphisms agreeing after adjacency, separately for each graph. Since a compact quantum group action is a unital complex algebra homomorphism into C(G) ⊗ C(H), this stronger assertion implies a negative answer to the question. The compact quantum group axioms and the action-to-homomorphism passage are explained here and are not formalized in this module.

**Theorem 1.6 (Rigidity for every finite twin-free graph).**

$$\forall (V: \operatorname{Type}), ([\operatorname{Fintype}\left(V\right)] \forall (G: \operatorname{SimpleGraph}\left(V\right)), ((\forall (x: V), (\forall (y: V), ((\forall (v: V), ((\operatorname{SimpleGraph.Adj}\left(G, x, v\right)) \Leftrightarrow (\operatorname{SimpleGraph.Adj}\left(G, y, v\right)))) \Rightarrow (x = y)))) \Rightarrow (\forall (B: \operatorname{Type}), ([\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)] \forall (\phi: \operatorname{AlgHom}\left(\mathbb{C}, V \to \mathbb{C}, B\right)), (\forall (\psi: \operatorname{AlgHom}\left(\mathbb{C}, V \to \mathbb{C}, B\right)), ((\forall (f: V \to \mathbb{C}), (\phi\left(\operatorname{adjacencyOperator}\left(G, f\right)\right) = \psi\left(\operatorname{adjacencyOperator}\left(G, f\right)\right))) \Rightarrow (\phi = \psi)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.algHom_eq_of_adjacency_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan (2025). *Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings*. DOI: [10.48550/arXiv.2502.10521](https://doi.org/10.48550/arXiv.2502.10521). URL: <https://arxiv.org/abs/2502.10521v2>.

*Commentary.*

Fix a vertex x. Multiply its adjacent neighbourhood indicators and the complements of its nonadjacent neighbourhood indicators. At x every factor is one. At any other vertex y, injectivity of adjacency rows supplies a factor that vanishes. Thus this product is Pi.single x 1. The equalizer subalgebra of the two homomorphisms contains all neighbourhood indicators, hence these products and all point indicators. Every function is the sum of its values times the point indicators, so the equalizer is the whole function algebra.

**Theorem 1.7 (None of the three graphs has quantum twins).**

$$\forall (B: \operatorname{Type}), ([\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)] (\neg (\operatorname{HasTwinsIn}\left(\operatorname{prism}, B\right))) \land ((\neg (\operatorname{HasTwinsIn}\left(\operatorname{cycleProduct}, B\right))) \land (\neg (\operatorname{HasTwinsIn}\left((\{\operatorname{Adj} := \lambda (u: \operatorname{Fin}\left(4\right) \to \operatorname{Bool}) \mapsto (\lambda (v: \operatorname{Fin}\left(4\right) \to \operatorname{Bool}) \mapsto (\operatorname{hammingDist}\left(u, v\right) = 1)), \operatorname{symm} := ..., \operatorname{loopless} := ...\}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(4\right) \to \operatorname{Bool}\right)), B\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.result` (`✓ std3`). ∎

*Resolves.* `Problems/bochniak-chelstowski-kasprzak-soltan-2025-quantum-twin-vertices` (proved) by `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bochniak-chelstowski-kasprzak-soltan-2025-quantum-twin-vertices","declaration_gid":"D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arkadiusz Bochniak; Igor Chełstowski; Paweł Kasprzak; Piotr M. Sołtan (2025). *Quantum Mycielskians: symmetries, twin vertices and distinguishing labelings*. DOI: [10.48550/arXiv.2502.10521](https://doi.org/10.48550/arXiv.2502.10521). URL: <https://arxiv.org/abs/2502.10521v2>.

*Commentary.*

The adjacency rows of each of the three graphs are distinct. Apply the rigidity theorem to each graph and to every complex target algebra B. This excludes the two distinct homomorphisms required by HasTwinsIn. The proof uses no invertibility of the adjacency matrix. The general rigidity theorem covers every finite simple graph whose ordinary twin classes are singletons.

## References

- Truth anchor: `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.HasTwinsIn`
- Truth anchor: `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.adjacencyOperator`
- Truth anchor: `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.algHom_eq_of_adjacency_eq`
- Truth anchor: `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.claim`
- Truth anchor: `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.cycleProduct`
- Truth anchor: `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.prism`
- Truth anchor: `D5/S3/Quantum/BochniakChelstowskiKasprzakSoltanQuantumTwins.result`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube](../Combinatorics/Graph/Hypercube.md)
