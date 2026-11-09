# Higher-body Bose support propagation

## Abstract

Higher-body Bose support propagation

I and L are finite register and local-label types. All traces are the actual unnormalized tensor partial traces. Hansenne-Xu-Kraft-Guehne own the marginal-to-global support mechanism; the supplied application note is by Haobo Ma and Wenlin Zhang, in that order.

**Theorem 1.1 (subsystem support).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.subsystem_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.subsystem_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Bose-supported actual subsystem marginal of a positive operator forces support of that operator under the lifted subsystem projector. The proof uses positive trace duality and the existing zero-weight support face, including singular and zero operators.

**Theorem 1.2 (pairs of subsystem support).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.pairs_of_subsystem_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.pairs_of_subsystem_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ordered pair inside a Bose-supported subsystem marginal has actual pair-Bose support. No product-state or diagonal-state premise is imposed.

**Definition 1.3 (hyperedgeGraph).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.hyperedgeGraph`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.hyperedgeGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two distinct registers are adjacent exactly when they lie together in one of the selected subsets. Empty and singleton subsets add no edge.

**Theorem 1.4 (support of connected hyperedges).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.support_of_connected_hyperedges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.support_of_connected_hyperedges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If this union-of-cliques graph is connected and every selected subsystem marginal is Bose-supported, positivity gives full Bose support and equality of all ordered pair marginals. The result allows arbitrary finite selected families and retains uncovered and isolated-register boundaries through the graph hypothesis.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.hyperedgeGraph`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.pairs_of_subsystem_support`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.subsystem_support`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.support_of_connected_hyperedges`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector](BoseComponentProjector.md)
