# Component Bose projectors

## Abstract

Tensor factorization of the graph component Bose projector in the original tensor basis.

The register type I and local alphabet L are finite. G is any simple graph on I. All matrices below use computational tensor words I to L. The construction keeps every connected component, including isolated vertices.

**Definition 1.1 (The tensor product over connected components).**

$$\operatorname{tensorProjector}\left(G, x, y\right)=\operatorname{ProductOverComponents}\left(G, P, x, y\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.tensorProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each connected component C, restrict x and y to its vertex set and evaluate the existing symmetric projector P on those restricted words. The matrix entry is the product of these entries over all C. This is the tensor product transported back to the original register basis. No reordering or normalization factor is inserted. A singleton component contributes the identity on its local register; the empty product is one.

**Theorem 1.2 (The component average equals the tensor product).**

$$\operatorname{componentProjector}\left(G\right)=\operatorname{tensorProjector}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite graph, the actual component-preserving permutation average is exactly this tensor-product matrix. The proof constructs the equivalence between component-preserving permutations and independent permutations of each component, factors the permutation-matrix entries, and reindexes the finite average. The cardinality factor is the product of the component permutation cardinalities. The theorem assumes neither connectedness nor a nonempty vertex set.

**Theorem 1.3 (Disconnected components admit a rank-one boundary).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.disconnected_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.disconnected_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement fixes the word w by assigning one basis label on the component of a and a distinct label elsewhere, and asserts positivity, all edge support constraints and failure of full support for the actual projector |w><w|. The sole edge on registers 0 and 1 with labels 0,0,1 specializes to the original three-qubit boundary. The proof uses exact tensor entries and projector identities.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.disconnected_counterexample`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.factorization`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.tensorProjector`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension](DickeExtension.md)
