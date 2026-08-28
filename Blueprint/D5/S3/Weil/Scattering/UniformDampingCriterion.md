# Uniform Damping Criterion

## Abstract

At the minimal shift, uniform damping one half is equivalent to the critical-line condition.

**Theorem 1.1 (Uniform damping is the critical-line condition).**

$$\forall Z: \operatorname{ZeroData}, \left(\forall n \in \mathbb {N},\; \Re(Z.zero(n)) = \operatorname{criticalAbscissa}\left(\right)\right) \Leftrightarrow \left(\forall n \in \mathbb {N},\; \frac{1}{2} + \Re(Z.zero(n)) - \operatorname{criticalAbscissa}\left(\right) = \frac{1}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/UniformDampingCriterion.uniform_damping_iff_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The damping rate transported from an enumerated zero at the minimal shift is written as one half plus its real part minus the critical abscissa. Uniform rate one half for every index is equivalent to equality of every zero real part with that abscissa.

## References

- Truth anchor: `D5/S3/Weil/Scattering/UniformDampingCriterion.uniform_damping_iff_critical_line`
