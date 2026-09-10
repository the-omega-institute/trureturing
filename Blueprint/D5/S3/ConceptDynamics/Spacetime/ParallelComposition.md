# Parallel Archive Composition

## Abstract

Parallel Archive Composition.

**Definition 1.1 (Complete tagged archive composition).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.parallel`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.parallel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both complete archives are copied using literal tags zero and one. All four attributes and only the internal causal relations are copied. Current regions and selections use the same tagged disjoint union.

**Theorem 1.2 (Parallel readout is additive).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.q_parallel`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.q_parallel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual selected signed sum separates over the two disjoint components. The background theorem uses the entire current regions, and balanced inputs remain balanced. All statements include empty archives and empty selections.

**Definition 1.3 (Old archives and their tags are retained).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.embeddingLeft`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.embeddingLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both input archives have attribute-preserving order embeddings. Event membership recovers each tagged component, and archive cardinality is the sum of the input cardinalities. These equalities retain the data required for later raw cancellation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.embeddingLeft`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.parallel`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ParallelComposition.q_parallel`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TaggedPresentation](TaggedPresentation.md)
