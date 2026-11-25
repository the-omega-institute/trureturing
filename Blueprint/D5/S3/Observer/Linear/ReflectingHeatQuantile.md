# Signed right-endpoint quadrature

## Abstract

Signed quadrature errors for equal-mass bins of the canonical heat multiplier.

**Theorem 1.1 (Kernels with one minimum).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density has unit mass in each bin. For a kernel that decreases to a minimum and then increases to zero, the right-endpoint sum minus its weighted integral is bounded above by minus the kernel at the minimum. On each finite prefix the bound telescopes from the minimum to the larger of the minimum location and the final endpoint. Absolute convergence passes the inequality to the half-line.

**Theorem 1.2 (Decreasing kernels).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a kernel decreasing to zero, the lower and upper endpoint values bound the integral on each bin. The signed error on a finite prefix is between the difference of its terminal and initial endpoint values and zero. On the half-line the lower bound is minus the value at the initial endpoint.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_antitone`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_le`
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatInterpolation](ReflectingHeatInterpolation.md)
