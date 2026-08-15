# Unit Escape Probability

## Abstract

Unit escape probability exactly characterizes fixed-point-free twists on nonempty address sets.

**Theorem 1.1 (Escape probability one characterizes fixed-point-free twists).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y \to Y, \forall A\in \mathbb{N}, 0 < A \Rightarrow (\operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right) = 1 \iff \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/UnitProbabilityCharacterization.escape_probability_eq_one_iff_fixed_point_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen closed form shows that probability one forces the fixed-point ratio to vanish when the address set is nonempty. Conversely, the existing fixed-point-free theorem gives unit escape probability directly.

Repository search found only the sufficient direction. Pinned Mathlib supplies the nonnegative power-one characterization and the elementary subtraction and division zero laws used in the converse.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/UnitProbabilityCharacterization.escape_probability_eq_one_iff_fixed_point_free`
- Dependency: [D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit](PoissonDomainLimit.md)
