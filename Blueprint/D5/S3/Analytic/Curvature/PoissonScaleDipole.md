# Poisson Scale Dipole

## Abstract

The off-line curvature dipole is the scale derivative of the Poisson kernel.

**Theorem 1.1 (The off-line curvature dipole is a Poisson scale derivative).**

$$\forall delta, gamma \in \operatorname{Real}\left(\right),\\{}0 < delta \Rightarrow\\{}\operatorname{let} poissonKernel := (scale, x \mapsto \frac{scale}{pi \times ((scale)^{2} + (x)^{2})}),\\{}\operatorname{let} curvatureDipole := (t \mapsto 2 \times \frac{(t - gamma)^{2} - (delta)^{2}}{((t - gamma)^{2} + (delta)^{2})^{2}}),\\{}\left(\forall t \in \operatorname{Real}\left(\right),\; curvatureDipole\left(t\right) = 2 \times pi \times \operatorname{deriv}\left((scale \mapsto poissonKernel\left(scale, t - gamma\right)), delta\right)\right) \land \left(\operatorname{Integrable}\left(curvatureDipole\right) \land \operatorname{integral}\left(t, \operatorname{Real}\left(\right), curvatureDipole\left(t\right), \operatorname{volume}\left(\right)\right) = 0\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Curvature/PoissonScaleDipole.poisson_scale_dipole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise identity differentiates the actual real Poisson kernel in its positive scale parameter. Integrability and zero total mass are transported from the frozen off-line curvature theorem, so this is a representation bridge and introduces no RH premise.

## References

- Truth anchor: `D5/S3/Analytic/Curvature/PoissonScaleDipole.poisson_scale_dipole`
- Dependency: [D5/S3/Analytic/Adelic/OffLineCurvatureDipole](../Adelic/OffLineCurvatureDipole.md)
