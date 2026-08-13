# Skewed Escape Mass

## Abstract

A one-slot skewed escape mass is one minus the fixed-output mass.

**Theorem 1.1 (One-slot escape mass complements fixed-output mass).**

$$\forall q, f, escapeMass(q, f) = 1 - fixedMass(q, f).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/SkewedEscapeMass.escape_mass_eq_one_sub_fixed_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite output type with a probability mass function q and an output transformation f, escapeMass sums q over outputs changed by f, while fixedMass sums q over outputs fixed by f.

The proof uses the finite filter partition identity and PMF.tsum_coe, so the two output classes exhaust total mass one.

This is an honest partial closure of clause (iv), the A = 1 edge case, of priced-interface theorem 7.1'. The general independent-slot product formula, pairwise intersection formula, uniform specialization, and engineering corollary remain unresolved.

## References

- Truth anchor: `D5/S0/Asymptotics/SkewedEscapeMass.escape_mass_eq_one_sub_fixed_mass`
