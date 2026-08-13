# Integer-Power Golden Norm

## Abstract

The golden norm of every integral power of the distinguished unit is the corresponding signed unit power.

**Theorem 1.1 (Norm of an integral power of phiUnit).**

$$\forall n\in\mathbb{Z},\ \operatorname{norm}((phiUnit^n:\operatorname{GoldenInt}^{\times}).val) = ((-1)^n:\mathbb{Z}^{\times}).val.$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Powers/IntegerPowerNorm.norm_phiUnit_zpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinguished golden unit phiUnit has value phi. Mapping its integer powers through the frozen norm monoid homomorphism gives the corresponding power of the unit -1 in the integer units; the displayed `.val` extracts the integer.

The proof uses Units.map and MonoidHom.map_zpow, so negative exponents are handled by the unit inverse rather than by a new norm definition.

This closes the integer-power extension clause of remark 27.722. The even-power positivity and cone-selection consequences remain unresolved.

## References

- Truth anchor: `D5/S0/Carrier/Powers/IntegerPowerNorm.norm_phiUnit_zpow`
- Dependency: [D5/S0/Carrier/Units](../Units.md)
