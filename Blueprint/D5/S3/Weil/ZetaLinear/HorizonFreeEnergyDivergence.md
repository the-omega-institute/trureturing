# Single-Defect Horizon Free-Energy Divergence

## Abstract

A nonzero single-defect depth has a positive horizon determinant exactly inside the horizon, and its negative-log free energy diverges at the boundary.

**Theorem 1.1 (The horizon free energy diverges universally).**

$$\forall delta \in \mathbb{R}_{\geq0}, delta \neq 0 \Rightarrow ((\forall omega, \operatorname{D}(delta, omega) = \frac{delta^2-omega^2}{delta^2}) \land (\forall omega, (0 < \operatorname{D}(delta, omega) \iff \lvert omega\rvert < \lvert delta\rvert)) \land (\forall omega, (\operatorname{D}(delta, omega) = 0 \iff \lvert omega\rvert = \lvert delta\rvert)) \land \lim_{omega\to delta^{-}} \operatorname{F}(delta, omega) = \infty).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/HorizonFreeEnergyDivergence.single_defect_horizon_free_energy_universal_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero nonnegative defect depth delta, field normalization gives the determinant D_delta(omega) = (delta^2 - omega^2) / delta^2. Its sign and zero locus are therefore controlled exactly by the absolute-value horizon inequalities.

On approach to the positive horizon from below, the determinant stays positive and tends to zero. Mathlib's right-hand logarithm limit then sends -log D_delta to positive infinity.

The Lean module also checks delta=2 at omega=1 and omega=2 exactly, and provides the explicit sequence omega_n=2-1/(n+1) as a nonvacuous witness of the divergence.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/HorizonFreeEnergyDivergence.single_defect_horizon_free_energy_universal_divergence`
