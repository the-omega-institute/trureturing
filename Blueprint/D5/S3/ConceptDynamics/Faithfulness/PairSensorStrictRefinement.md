# Pair Sensor Strict Refinement

## Abstract

A second sensor strictly refines the first kernel when it resolves a collision.

**Theorem 1.1 (A resolved collision makes the paired kernel strictly finer).**

$$\forall first: X \to Y, second: X \to Z, x, y: X,\\{}(\operatorname{first}\left(x\right) = \operatorname{first}\left(y\right) \land \operatorname{second}\left(x\right) \neq \operatorname{second}\left(y\right)) \Rightarrow \operatorname{ker}\left(state \mapsto (\operatorname{first}\left(state\right), \operatorname{second}\left(state\right))\right) < \operatorname{ker}\left(first\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/PairSensorStrictRefinement.pair_sensor_strictly_refines_first_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairing two sensors can only refine the first sensor's equality kernel, because equality of pairs implies equality of first components.

Assume x and y collide under the first sensor but are separated by the second. Their collision belongs to the first kernel and not the paired kernel.

That explicit witness proves strict inclusion; no global injectivity of the second sensor is required.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/PairSensorStrictRefinement.pair_sensor_strictly_refines_first_kernel`
