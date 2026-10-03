# Golden Units

## Abstract

Golden integers are units exactly when their norm is positive or negative one.

**Theorem 1.1 (Unit criterion).**

$$\forall x\in\operatorname{GoldenInt},\operatorname{IsUnit}(x)\iff N(x)=1\lor N(x)=-1$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Units.isUnit_iff_norm_eq_one_or_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An element of the golden integer ring is invertible precisely when its integer norm is one or minus one. Conjugation supplies its inverse, with a sign change in the second case.

**Theorem 1.2 (Norm of golden-ratio powers).**

$$N{\varphi^n} = {-1}^n$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Units.norm_phi_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural exponent, multiplicativity of the norm gives the alternating value exactly.

`D5/S0/Carrier/Units` proves the exact executable criterion `IsUnit x <-> N(x)=1 or N(x)=-1`. In the forward direction, the multiplicative norm maps units to integer units. In the reverse direction, conjugation gives an explicit inverse, with one sign correction when the norm is negative.

The module packages `phi` as a unit with inverse `phi-1`, proves `N(phi^n)=(-1)^n` for natural exponents, and proves that every member of the explicit family `+/-phi^n` is a unit for integral exponents.

## References

- Truth anchor: `D5/S0/Carrier/Units.isUnit_iff_norm_eq_one_or_neg_one`
- Truth anchor: `D5/S0/Carrier/Units.norm_phi_pow`
- Dependency: [D5/S0/Carrier/Norm](Norm.md)
