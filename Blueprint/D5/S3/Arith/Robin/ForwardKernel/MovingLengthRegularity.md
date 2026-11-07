# Regularity of variable-length profile averages

## Abstract

Integrable profiles admit measurable and square-integrable variable-length averages.

**Theorem 1.1 (Measurability for variable lengths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.profileAverage_variable_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.profileAverage_variable_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a locally bounded measurable E, an integrable Borel profile g, and a measurable real length H, the function sending x to the profile average at length H(x) and starting point x is measurable. The unit-interval formula expresses its numerator as a parameter integral of a jointly measurable function.

**Theorem 1.2 (Square integrability for bounded positive lengths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.profileAverage_variable_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.profileAverage_variable_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite ordered interval [a,b], suppose the measurable length H lies between fixed l>0 and L. For any integrable Borel profile g, its variable-length average belongs to L squared. A compact bound B for E on [a,b+L] bounds the absolute average by 2B times the L1 norm of g divided by l.

**Theorem 1.3 (Integrability in the step).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.step_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.step_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each starting point x, increments of a locally bounded measurable E are integrable as functions of their step on every finite oriented interval.

**Theorem 1.4 (Square integrability in the step).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.step_sq_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.step_sq_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each starting point x, the square of the increment of a locally bounded measurable E is integrable as a function of its step on every finite oriented interval.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.profileAverage_variable_measurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.profileAverage_variable_memLp`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.step_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.step_sq_integrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
