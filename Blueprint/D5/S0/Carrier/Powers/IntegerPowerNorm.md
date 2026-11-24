# Integer-Power Golden Norm

## Abstract

The golden norm of every integral power of the distinguished unit is the corresponding signed unit power.

**Theorem 1.1 (Norm of an integral power of phiUnit).**

$$\forall n\in\mathbb{Z},\ \operatorname{norm}((phiUnit^n:\operatorname{GoldenInt}^{\times}).val) = ((-1)^n:\mathbb{Z}^{\times}).val.$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Powers/IntegerPowerNorm.norm_phiUnit_zpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinguished golden unit phiUnit has value phi. The strict golden power uses phi for nonnegative exponents and its inverse for negative exponents. Both bases have norm -1.

The proof applies natural-power norm multiplicativity in each integer case. It raises -1 to the absolute exponent because -1 is its own inverse.

This closes the integer-power extension clause of remark 27.722. The even-power positivity and cone-selection consequences remain unresolved.

## References

- Truth anchor: `D5/S0/Carrier/Powers/IntegerPowerNorm.norm_phiUnit_zpow`
