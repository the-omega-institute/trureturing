# Golden Units

## Abstract

Golden integers are units exactly when their norm is positive or negative one.

**Theorem 1.1 (Norm of golden-ratio powers).**

$$N{\varphi^n} = {-1}^n$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Units.norm_phi_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural exponent, multiplicativity of the norm gives the alternating value exactly.

`D5/S0/Carrier/Units` proves the exact executable criterion `IsUnit x <-> N(x)=1 or N(x)=-1`. In the forward direction, the multiplicative norm maps units to integer units. In the reverse direction, conjugation gives an explicit inverse, with one sign correction when the norm is negative.

The module packages `phi` as a unit with inverse `phi-1`, proves `N(phi^n)=(-1)^n` for natural exponents, and proves that every member of the explicit family `+/-phi^n` is a unit for integral exponents.

## References

- Truth anchor: `D5/S0/Carrier/Units.norm_phi_pow`
- Dependency: [D5/S0/Carrier/Norm](Norm.md)
