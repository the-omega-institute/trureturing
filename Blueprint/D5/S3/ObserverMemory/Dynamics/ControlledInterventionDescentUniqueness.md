# Controlled Intervention Descent Uniqueness

## Abstract

Every controlled update descends uniquely through canonical behavior completion.

**Theorem 1.1 (All controlled updates descend uniquely).**

$$\forall Y, U, O,\ F: U \to Y \to Y, q: Y \to O,\ \forall u\in U, \exists! \overline{F}_{u}: \operatorname{ControlledCompletion}(F, q) \to \operatorname{ControlledCompletion}(F, q),\\{}\operatorname{completionProjection}\left(F, q\right) \circ F(u) = \overline{F}_{u} \circ \operatorname{completionProjection}\left(F, q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/ControlledInterventionDescentUniqueness.all_interventions_unique_completion_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical quotient by equality of every finite-word readout, and pi is its canonical projection. No separate completion or projection primitive is introduced.

For every control u, there is exactly one endomap of the completion that makes the update square commute. Existence is witnessed by the canonical completion update; uniqueness follows from surjectivity of the quotient projection.

Pointwise table and output projections lift this unique underlying square to the source's simultaneous diagonal naturality law.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/ControlledInterventionDescentUniqueness.all_interventions_unique_completion_descent`
- Dependency: [D5/S0/Rewriting/Quotients/DynamicsDescent](../../../S0/Rewriting/Quotients/DynamicsDescent.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../Prediction/ControlledBehaviorUniversality.md)
