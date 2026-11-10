# Regularity of forward averages

## Abstract

Local interval integrability.

**Theorem 1.1 (Local interval integrability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.locallyBoundedMeasurable_intervalIntegrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.locallyBoundedMeasurable_intervalIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A measurable real function bounded on each compact interval is integrable on every finite oriented interval.

**Theorem 1.2 (Continuity of window averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.windowAverage_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.windowAverage_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For R>0, the forward window average of a locally bounded measurable real function is continuous. Expressing it as the difference of values of its continuous integral primitive proves this without differentiability of the original function.

**Theorem 1.3 (Continuity from interval integrability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.windowAverage_continuous_of_intervalIntegrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.windowAverage_continuous_of_intervalIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a real function is interval integrable on every finite interval, each of its forward window averages is continuous. The proof writes the average as a difference of values of the continuous integral primitive.

**Theorem 1.4 (Derivative of a double average).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.doubleAverage_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.doubleAverage_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For R>0, the double forward average of E has derivative at every x equal to the window average of E(y+R)-E(y), evaluated at x and divided by R. The fundamental theorem of calculus applies to the continuous first average.

**Theorem 1.5 (Continuous differentiability of double averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.doubleAverage_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.doubleAverage_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For R>0, a double forward average of a locally bounded measurable real function is continuously differentiable. Its derivative is the difference of two translates of the continuous first average, divided by R.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.doubleAverage_contDiff`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.doubleAverage_hasDerivAt`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.locallyBoundedMeasurable_intervalIntegrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.windowAverage_continuous`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.windowAverage_continuous_of_intervalIntegrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs](CrossExponentDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
