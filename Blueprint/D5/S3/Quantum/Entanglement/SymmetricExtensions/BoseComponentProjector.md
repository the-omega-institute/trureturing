# Component Bose projectors

## Abstract

Tensor factorization of the graph component Bose projector in the original tensor basis.

The register type I and local alphabet L are finite. G is any simple graph on I. All matrices below use computational tensor words I to L. The construction keeps every connected component, including isolated vertices.

For each connected component C, restrict the computational words x and y to C and take the existing symmetric-projector entry P on those restrictions. Multiplying over all components, including singleton components and the empty product, gives the component tensor expression in the original register basis. No reordering or normalization factor is inserted.

The component-preserving permutation average is reindexed by the product of the component permutation groups; entrywise factorization and the product cardinality identity give the same expression for every finite graph, without connectedness or nonemptiness assumptions.

**Theorem 1.1 (Disconnected components admit a rank-one boundary).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.disconnected_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.disconnected_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement fixes the word w by assigning one basis label on the component of a and a distinct label elsewhere, and asserts positivity, all edge support constraints and failure of full support for the actual projector |w><w|. The sole edge on registers 0 and 1 with labels 0,0,1 specializes to the original three-qubit boundary. The proof uses exact tensor entries and projector identities.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.disconnected_counterexample`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension](DickeExtension.md)
