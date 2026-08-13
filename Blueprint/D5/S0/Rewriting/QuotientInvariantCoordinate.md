# Quotient Invariant Coordinate

## Abstract

A complete invariant gives a separating coordinate on equivalence classes.

**Theorem 1.1 (Complete invariants separate quotient classes).**

$$\forall alpha, beta, r: \operatorname{Setoid}(alpha), f: alpha \to beta, (\forall x, y: alpha, f(x) = f(y) \Leftrightarrow r(x, y)) \Rightarrow \operatorname{Injective}(\operatorname{QuotientLift}_r(f)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/QuotientInvariantCoordinate.quotient_invariant_coordinate_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completeness hypothesis says that two objects have equal invariant values exactly when they are equivalent. Mathlib's quotient-lift characterization then makes the induced class coordinate injective. This closes only the quotient-coordinate clause; canonical representatives, classification examples, and metatheoretic self-application claims remain unresolved.

## References

- Truth anchor: `D5/S0/Rewriting/QuotientInvariantCoordinate.quotient_invariant_coordinate_injective`
