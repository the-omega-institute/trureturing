# Integer Recovery And Structure Separation

## Abstract

CRT recovery and the spectral layer compose, but similarity retains a witness.

**Definition 1.1 (Local residue agreement).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.localResiduesAgree`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.localResiduesAgree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two bounded integer values have identical prime-power residue readouts.

**Definition 1.2 (Bounded integer trace data).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.boundedIntegerTraceData`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.boundedIntegerTraceData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace-code family uses the exact Fin N carrier from the CRT theorem.

**Definition 1.3 (Initial power-trace agreement).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.initialPowerTracesAgree`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.initialPowerTracesAgree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first n positive matrix power traces agree.

**Definition 1.4 (Newton characteristic-polynomial bridge).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.NewtonCharacteristicPolynomialBridge`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.NewtonCharacteristicPolynomialBridge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This explicit premise records the forward trace-to-charpoly step, which the imported saturation theorem does not provide.

**Definition 1.5 (All positive power-trace agreement).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.positivePowerTracesAgree`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.positivePowerTracesAgree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every positive matrix power has the same trace.

**Theorem 1.6 (The bounded CRT layer has no residual).**

$$localResiduesAgree \Rightarrow equal.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.local_residue_recovery_is_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under pointwise prime support and a product capacity bound, equal local residues force equality of the bounded integer values.

**Theorem 1.7 (Integer recovery then structure recovery).**

$$localResidues \Rightarrow integerTraces \Rightarrow charpoly \land allTraces.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.integer_recovery_structure_recovery_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Residues and height recover the trace codes; alignment and the explicit Newton bridge recover the characteristic polynomial; imported saturation then recovers all positive traces.

**Theorem 1.8 (Dimension one has no Jordan residual).**

$$charpolyEqual \Rightarrow conjugate.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.one_dimensional_charpoly_determines_similarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one-by-one matrices, equal characteristic polynomials force equality and therefore conjugacy.

**Theorem 1.9 (The two-dimensional residual witness).**

$$charpolyEqual \land notConjugate.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.power_trace_similarity_residual_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported zero matrix and nonzero square-zero block have equal characteristic polynomial but are not conjugate.

**Theorem 1.10 (Prime support is necessary).**

$$primeSupportNecessary : Prop.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.prime_support_is_necessary_for_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Overlapping nonprime coordinates make the product-capacity criterion false, as witnessed by the imported concrete pair.

**Theorem 1.11 (The height bound is necessary).**

$$heightBoundNecessary : Prop.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.height_bound_is_necessary_for_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Without capacity, empty support identifies two distinct values in Fin 2.

**Theorem 1.12 (Height zero is vacuously injective).**

$$zeroHeightFirstLayer : Prop.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.zero_height_bound_first_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At height zero the bounded carrier is empty, so every residue readout is injective.

**Theorem 1.13 (The Newton bridge is necessary).**

$$newtonBridgeNecessary : Prop.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.newton_bridge_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In characteristic two, zero and identity have equal first traces but different characteristic polynomials.

**Theorem 1.14 (Trace alignment is necessary).**

$$traceAlignmentNecessary : Prop.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.trace_alignment_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal residue codes alone can be unrelated to matrix traces, even when a vacuous Newton bridge holds.

**Theorem 1.15 (The zero-dimensional audit).**

$$zeroDimensionChain : Prop.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.zero_dimension_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Fin 0, the trace family is empty and the composed conclusion remains valid.

**Theorem 1.16 (Zero and identity audits).**

$$zeroIdentityLayerAudit : Prop.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.zero_and_identity_layer_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Empty support is injective only on the singleton window; zero and identity are separated by charpoly and conjugacy.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.NewtonCharacteristicPolynomialBridge`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.boundedIntegerTraceData`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.height_bound_is_necessary_for_chain`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.initialPowerTracesAgree`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.integer_recovery_structure_recovery_chain`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.localResiduesAgree`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.local_residue_recovery_is_exact`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.newton_bridge_is_necessary`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.one_dimensional_charpoly_determines_similarity`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.positivePowerTracesAgree`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.power_trace_similarity_residual_witness`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.prime_support_is_necessary_for_chain`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.trace_alignment_is_necessary`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.zero_and_identity_layer_audit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.zero_dimension_chain`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.zero_height_bound_first_layer`
- Dependency: [D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation](../../../S0/Observation/PowerTraceCharacteristicPolynomialSaturation.md)
- Dependency: [D5/S0/Observation/PowerTraceSimilarityCountermodel](../../../S0/Observation/PowerTraceSimilarityCountermodel.md)
- Dependency: [D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness](../../Factorization/PrimePowers/BoundedIntegerCrtCompleteness.md)
