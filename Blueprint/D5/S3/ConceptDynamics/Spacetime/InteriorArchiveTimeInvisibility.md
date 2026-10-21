# Current Regions and Synchronized Prefixes

## Abstract

Current-region correspondences preserve temporal-free observations.

**Definition 1.1 (Current attributes, order and selection).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.CurrentIsoData`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.CurrentIsoData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A current correspondence is a bijection of current events preserving attributes, the induced causal relation and selection. Inactive archive events need not have matching attributes. Temporal-free operations retain such correspondences: parallel composition uses a disjoint sum, while generated product uses a product of current parents. Generated current events form a causal antichain.

**Theorem 1.2 (Both binary slots have an exact execution sequence).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.reify_temporal_free`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.reify_temporal_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite native word without temporal composition has a sequence of unary, parallel and product steps with exactly its Option denotation on every balanced input. Both slots are retained, and every fixed balanced parameter is allowed.

**Theorem 1.3 (Saturated prefixes have equal final charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.saturated_runSteps`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.saturated_runSteps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two current regions differ only in the time of one corresponding event with no incoming causal edge; position, sign, source and all selection bits agree. Collect the causal predicates before the first product and pull each back through preceding time shifts. Suppose every nonempty predicate is reached from the exceptional event on both sides, and both exceptional times lie below the first product threshold.

Unary filters then preserve matching selection bits. Parallel steps add identical disjoint components and cannot create new incoming edges. At the first product, the exceptional time is below every current parent time in the fixed factor, so corresponding generated attributes agree. This also covers an empty current factor. Every remaining temporal-free step preserves the current correspondence. Without any product, equal signs and selection already give equal charge.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.CurrentIsoData`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.reify_temporal_free`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.saturated_runSteps`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/CoarseObservation](CoarseObservation.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization](TotalCopyNormalization.md)
