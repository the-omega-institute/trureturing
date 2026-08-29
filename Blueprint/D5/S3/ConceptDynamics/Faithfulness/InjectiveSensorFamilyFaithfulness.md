# Injective Sensor Family Faithfulness

## Abstract

One injective sensor makes the complete sensor family faithful.

**Theorem 1.1 (An injective member makes the joint readout injective).**

$$\forall sensor: I \to \left(X \to O\right), i0: I, \operatorname{Injective}\left(\operatorname{sensor}\left(i0\right)\right) \Rightarrow \operatorname{Injective}\left(x \mapsto (i \mapsto \operatorname{sensor}\left(i, x\right))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/InjectiveSensorFamilyFaithfulness.injective_member_makes_joint_readout_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an indexed sensor family and select one sensor whose state readout is injective.

Equality of the complete function-valued readouts gives equality at the selected coordinate by evaluation.

Injectivity of that coordinate then identifies the source states. No condition is imposed on the other sensors or on the index type.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/InjectiveSensorFamilyFaithfulness.injective_member_makes_joint_readout_injective`
