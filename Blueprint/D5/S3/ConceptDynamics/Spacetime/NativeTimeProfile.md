# Native Time Profiles

## Abstract

Finite signed time profiles and exact native primitive updates.

**Definition 1.1 (Reflexive current successors).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.successors`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.successors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set retains complete timed attributes of the current event itself and all its current causal successors, including unselected targets.

**Definition 1.2 (Native event cell).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.cell`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A current event determines its timed attribute, selected Boolean bit, and finite successor attribute set.

**Definition 1.3 (Signed finite time profile).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum signed singleton cell measures over every current event. Noncurrent archive events contribute no cells. Events in the same cell add their integer coefficients.

**Definition 1.4 (Linear cell transport).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.push`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.push` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport a finitely supported integer profile along a cell map, adding coefficients when cells merge.

**Definition 1.5 (Terminal selected charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This integer linear functional weights selected cells by one and unselected cells by zero.

**Theorem 1.6 (Terminal readout equals native charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout_gamma`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout_gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rich native history, applying the selected-cell functional to its complete time profile gives precisely its native q readout.

**Definition 1.7 (Integer attribute shift).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.shiftAttribute`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.shiftAttribute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add an arbitrary integer to time while preserving position, sign and source.

**Definition 1.8 (All five unary updates).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.unaryCell`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.unaryCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complement flips selection. Spatial and source filters conjoin their predicate with selection. Causal filtering tests whether the successor set hits the fixed timed-attribute predicate. Shifting changes both the own attribute and every successor attribute.

**Theorem 1.9 (Native unary operations are linear pushes).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_unary`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_unary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every balanced history and every native unary primitive, the actual output time profile equals the corresponding linear push of the input profile.

**Theorem 1.10 (Parallel profiles add).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_parallel`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_parallel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of balanced histories, the complete profile of their tagged parallel composite is the sum of the two profiles. Actual current events are reindexed; each component retains its successor set.

**Definition 1.11 (Generated product attribute).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productAttribute`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productAttribute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Generated time is the maximum parent time plus one. Positions add, signs multiply via Boolean equality, and sources form the ordered tree product.

**Definition 1.12 (Generated product cell).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productCell`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parent selection bits conjoin. The successor set of a newly generated current event is the singleton containing its own generated attribute.

**Definition 1.13 (Bilinear cell push).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productPush`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productPush` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extend the generated cell operation by integer bilinearity in the two finitely supported profiles.

**Theorem 1.14 (Native product equals the bilinear push).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_product`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of balanced histories, the actual generated-product profile equals the bilinear push of the two parent profiles. The proof uses the exact parent-pair current equivalence and absence of paths out of generated nodes.

**Definition 1.15 (Homogenized native profile).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.pack`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.pack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A balanced native history is embedded as the pair consisting of the integer one and its complete time profile. The extra coordinate represents constants in the multilinear syntax interpretation.

**Definition 1.16 (Multilinear interpretation of the copy syntax).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each input occurrence occupies a distinct multilinear coordinate. Constants use the empty coordinate family. Unary nodes use linear profile pushes. Binary nodes combine disjoint leaf families using bilinear homogenized parallel or product maps. Temporal nodes are assigned parallel semantics here; the correctness theorem explicitly requires temporal freedom.

**Theorem 1.17 (The multilinear model computes native evaluation).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model_eval`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arity, temporal-free copy term, independent balanced leaf assignment and successful native result, applying the multilinear model to the packed leaves gives exactly the packed result. Structural induction consumes the native unary, parallel and product profile updates. This connects the formal multilinear interpretation to the actual finite native histories.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.cell`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_parallel`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_product`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_unary`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model_eval`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.pack`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productAttribute`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productCell`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productPush`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.push`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout_gamma`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.shiftAttribute`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.successors`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.unaryCell`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/CoarseObservation](CoarseObservation.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization](TotalCopyNormalization.md)
