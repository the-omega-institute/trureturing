# Unit-Interval Reflection

## Abstract

Reflection about one half is an involution on the closed unit interval.

**Theorem 1.1 (Unit-interval reflection is an involution).**

$$\forall s\in[0, 1],\ \sigma(\sigma(s)) = s.$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/UnitIntervalReflection.unit_interval_reflection_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s in the closed real unit interval, the central reflection sigma(s) = 1 - s remains in that interval and applying sigma twice returns s.

Pinned Mathlib was searched before proving. unitInterval.symm_involutive is an exact hit, so the Lean declaration is a thin wrapper around that theorem; sub_sub_cancel is a related algebraic hit, and the repository has no existing wrapper for this unit-interval statement.

This is a continuation partial closure of the source remark, restricted to its s-to-one-minus-s exchange-involution clause. The weighted path integrals, time-reversal clauses, fluctuation law, extension to negative integer powers, and even-power cone selection remain unresolved.

## References

- Truth anchor: `D5/S0/Conventions/UnitIntervalReflection.unit_interval_reflection_involutive`
