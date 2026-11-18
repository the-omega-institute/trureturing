# Sharp power-kernel correction

## Abstract

An explicit sharp majorant for the correction to the power-kernel integral.

**Definition 1.1 (Correction majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correctionMajorant`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correctionMajorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The majorant is pi^2/(6*(1-pi^2/(6*s^2))). Its denominator is positive for s at least pi.

**Theorem 1.2 (Cubic sine bound for the correction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.kernel_correction_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.kernel_correction_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real s at least pi, s*(pi/sin(pi/s)-s) is nonnegative and at most the correction majorant. The cubic lower bound for sine preserves the coefficient one sixth.

**Theorem 1.3 (Sharp limiting majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correction_majorant_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correction_majorant_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correction majorant tends to pi^2/6 as s tends to positive infinity. This coefficient controls the localized prime-weight upper estimate. A matching lower bound for the second distinct-prime counting threshold is not established here.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correctionMajorant`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correction_majorant_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.kernel_correction_upper`
