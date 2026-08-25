# Intervention Completion Naturality

## Abstract

Every controlled intervention commutes with the canonical completion projection on diagonals.

**Theorem 1.1 (All interventions descend naturally to completion).**

$$\forall A, U, Y, O, update: U \to Y \to Y, readout: Y \to O, table: A\times A \to Y, \forall u\in U, \operatorname{pointwiseOutputProjection}(\operatorname{completionProjection}(update, readout), \operatorname{diagonalUpdate}(update(u), table)) = \operatorname{diagonalUpdate}(\operatorname{completionUpdate}(update, readout, u), \operatorname{pointwiseTableProjection}(\operatorname{completionProjection}(update, readout), table)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/InterventionCompletionNaturality.all_interventions_completion_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The table is updated on its diagonal by the chosen controlled intervention. The existing pointwise table and output projections use the canonical controlled behavior completion projection, while completionUpdate is its induced quotient transition.

For every intervention and every table, projecting the updated diagonal equals updating the projected diagonal. The identity is pointwise and follows from the quotient map computation rule.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/InterventionCompletionNaturality.all_interventions_completion_naturality`
- Dependency: [D5/S3/Observer/Naturality/DiagonalNaturalityDefect](../../Observer/Naturality/DiagonalNaturalityDefect.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../Prediction/ControlledBehaviorUniversality.md)
