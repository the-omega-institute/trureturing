# Reindexing the generator edges

## Abstract

Reindexing the generator edges

Incoming and outgoing edges are pairs of a Fin 4862 target and a Fin 8192 source. Lists preserve multiplicity. Their permutation identity reindexes the integer scalar sum in every additive commutative group.

**Definition 1.1 (incoming).**

$$\forall (i: \operatorname{Fin}\left(8192\right)), (\operatorname{incoming}\left(i\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{PonciniRasmussenCertificateTree}.\operatorname{get}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{PonciniRasmussenNineHorner}.\operatorname{rows}, \operatorname{Fin}.\operatorname{val}\left(i\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incoming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lookup uses the shared D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get and the single D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner.rows table. The index i has type Fin 8192 and the returned list has type List Nat.

**Theorem 1.2 (sparseHamiltonian_eq).**

$$\forall (v: (\operatorname{Fin}\left(8192\right)) \to (\operatorname{Int})), (\operatorname{sparseHamiltonian}\left(v\right) = ((i: \operatorname{Fin}\left(8192\right)) \mapsto -(\operatorname{List}.\operatorname{foldl}\left(((s: \operatorname{Int}) \mapsto ((j: \operatorname{Nat}) \mapsto (s) + (v\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Nat}.\operatorname{mod}\left(j, 8192\right), \operatorname{Nat}.\operatorname{mod_{lt}}\left(j, \operatorname{by} \operatorname{omega}\right)\right)\right)))), 0, \operatorname{incoming}\left(i\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparseHamiltonian_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

List.foldl adds the coefficient at each source index, then the Hamiltonian negates the sum.

**Definition 1.3 (incomingEdges).**

$$\operatorname{incomingEdges} = \operatorname{List}.\operatorname{flatMap}\left(((t: \operatorname{Fin}\left(4862\right)) \mapsto \operatorname{List}.\operatorname{map}\left(((s: \operatorname{Nat}) \mapsto \operatorname{Prod}.\operatorname{mk}\left(t, \operatorname{Fin}.\operatorname{mk}\left(\operatorname{Nat}.\operatorname{mod}\left(s, 8192\right), \operatorname{Nat}.\operatorname{mod_{lt}}\left(s, \operatorname{by} \operatorname{omega}\right)\right)\right)), \operatorname{incoming}\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(t\right), \operatorname{by} \operatorname{omega}\right): \operatorname{Fin}\left(8192\right))\right)\right)), \operatorname{List}.\operatorname{finRange}\left(4862\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incomingEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each source in a target row is reduced modulo 8192 with Nat.mod_lt providing the bound.

**Definition 1.4 (outgoingEdges).**

$$\operatorname{outgoingEdges} = \operatorname{List}.\operatorname{flatMap}\left(((s: \operatorname{Fin}\left(4862\right)) \mapsto \operatorname{List}.\operatorname{filterMap}\left(((g: \operatorname{Fin}\left(8\right)) \mapsto \operatorname{dite}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right) < 4862, ((ht: \operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right) < 4862) \mapsto \operatorname{Option}.\operatorname{some}\left(\operatorname{Prod}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right), ht\right), (\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(s\right), \operatorname{by} \operatorname{omega}\right): \operatorname{Fin}\left(8192\right))\right)\right)), \operatorname{Function}.\operatorname{const}\left(\operatorname{Not}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right) < 4862\right), \operatorname{Option}.\operatorname{none}\right)\right)), \operatorname{List}.\operatorname{finRange}\left(8\right)\right)), \operatorname{List}.\operatorname{finRange}\left(4862\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.outgoingEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only transitions with value below 4862 contribute an edge.

**Theorem 1.5 (edges_perm).**

$$\operatorname{List}.\operatorname{Perm}\left(\operatorname{incomingEdges}, \operatorname{outgoingEdges}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.edges_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both lists enumerate the same edges with the same multiplicities.

**Theorem 1.6 (sparse_sum).**

$$\forall (A: \operatorname{Type}), ([\operatorname{AddCommGroup}\left(A\right)] \forall (b: (\operatorname{Fin}\left(4862\right)) \to (A)), (\forall (v: (\operatorname{Fin}\left(8192\right)) \to (\operatorname{Int})), (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}\left(\right), ((t: \operatorname{Fin}\left(4862\right)) \mapsto \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{sparseHamiltonian}\left(v\right)\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(t\right), \operatorname{by} \operatorname{omega}\right): \operatorname{Fin}\left(8192\right))\right), b\left(t\right)\right))\right) = -(\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}\left(\right), ((s: \operatorname{Fin}\left(4862\right)) \mapsto \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}\left(\right), ((g: \operatorname{Fin}\left(8\right)) \mapsto \operatorname{dite}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right) < 4862, ((ht: \operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right) < 4862) \mapsto \operatorname{HSMul}.\operatorname{hSMul}\left(v\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(s\right), \operatorname{by} \operatorname{omega}\right): \operatorname{Fin}\left(8192\right))\right), b\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right), ht\right)\right)\right)), \operatorname{Function}.\operatorname{const}\left(\operatorname{Not}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right) < 4862\right), 0\right)\right))\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparse_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finset.sum binds t, s and g at their stated finite types. Both Fin embeddings and the target proof ht are explicit.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.edges_perm`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incoming`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incomingEdges`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.outgoingEdges`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparseHamiltonian_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparse_sum`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree](PonciniRasmussenCertificateTree.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams](PonciniRasmussenNineDiagrams.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
