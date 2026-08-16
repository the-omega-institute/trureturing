# Gauss Inverse Step

## Abstract

A Gauss history coordinate recovers the partial quotient that produced it.

**Theorem 1.1 (The inverse history step recovers its quotient).**

$$\forall a\in \mathbb{N}, y\in [0,1), \lfloor \frac{1}{\frac{1}{(a+y)}} \rfloor = a$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/GaussInverseStep.gauss_inverse_step_recovers_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a history coordinate y in the half-open unit interval, updating it to 1/(a+y) stores the partial quotient a: the integer floor of the reciprocal of the updated coordinate is exactly a. The proof combines Mathlib's involution of inversion with its floor law for an integer plus a value in [0,1). Only this inverse-step formula is asserted; no claim is made here about invertibility of the full natural extension, its invariant measure, or restart dynamics.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/GaussInverseStep.gauss_inverse_step_recovers_quotient`
