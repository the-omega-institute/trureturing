# Existence Layers Do Not Imply One Another

## Abstract

Finite countermodels separate type, interface, causal, and record existence.

**Theorem 1.1 (Type existence does not imply distinguishable existence).**

$$\exists X, O: \operatorname{Type},\ x, y: X,\ q: X \to O,\\\operatorname{TypeExistence}\left(x, y\right) \land \neg \operatorname{DistinguishableExistence}\left(q, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Existence/ExistenceLayersDoNotImply.type_existence_does_not_imply_distinguishable_existence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two Boolean states are genuinely different, so their distinction exists at the type level. A constant readout into the one-point type sends both states to the same output, so the interface cannot distinguish them.

**Theorem 1.2 (Distinguishable existence does not imply causal existence).**

$$\exists X, O: \operatorname{Type},\ T: X \to X,\ q: X \to O,\ x, y: X,\\\operatorname{DistinguishableExistence}\left(q, x, y\right) \land \neg \operatorname{CausalExistence}\left(T, q, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Existence/ExistenceLayersDoNotImply.distinguishable_existence_does_not_imply_causal_existence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity readout separates the two Boolean states at the present time. A constant update maps both states to false after one step, so every positive-time readout agrees and the distinction has no causal existence.

**Theorem 1.3 (Causal existence does not imply record existence).**

$$\exists X, O, R: \operatorname{Type},\ T: X \to X,\ q: X \to O,\ record: X \to R,\ x, y: X,\\\operatorname{CausalExistence}\left(T, q, x, y\right) \land (\forall z, \operatorname{record}\left(\operatorname{T}\left(z\right)\right) = \operatorname{record}\left(z\right)) \land \neg \operatorname{RecordExistence}\left(T, record, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Existence/ExistenceLayersDoNotImply.causal_existence_does_not_imply_record_existence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity dynamics preserve two distinct Boolean states, and the identity readout separates them after one positive-time step. A constant record into the one-point type is stable under those dynamics but assigns the same record to both states, so record existence fails.

## References

- Truth anchor: `D5/S3/Observer/Existence/ExistenceLayersDoNotImply.causal_existence_does_not_imply_record_existence`
- Truth anchor: `D5/S3/Observer/Existence/ExistenceLayersDoNotImply.distinguishable_existence_does_not_imply_causal_existence`
- Truth anchor: `D5/S3/Observer/Existence/ExistenceLayersDoNotImply.type_existence_does_not_imply_distinguishable_existence`
