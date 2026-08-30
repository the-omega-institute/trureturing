# Off-Line Curvature Dipole

## Abstract

A reflected pair of logarithmic squared-distance potentials has an explicit zero-mass curvature with a negative core and positive wings.

**Theorem 1.1 (A reflected logarithmic pair produces a curvature dipole).**

$$\forall delta, gamma \in \operatorname{Real}\left(\right),\\{}0 < delta \Rightarrow\\{}\operatorname{let} potential := (u, t \mapsto \frac{\operatorname{log}\left((u - delta)^{2} + (t - gamma)^{2}\right)}{2} + \frac{\operatorname{log}\left((u + delta)^{2} + (t - gamma)^{2}\right)}{2}),\\{}\operatorname{let} curvature := (t \mapsto \operatorname{deriv}\left(\operatorname{deriv}\left((u \mapsto potential\left(u, t\right))\right), 0\right)),\\{}\left(\forall t \in \operatorname{Real}\left(\right),\; curvature\left(t\right) = 2 \times \frac{(t - gamma)^{2} - (delta)^{2}}{((t - gamma)^{2} + (delta)^{2})^{2}}\right) \land \left(curvature\left(gamma\right) = -\frac{2}{(delta)^{2}} \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; curvature\left(t\right) = 0 \Leftrightarrow \left(t = gamma - delta \lor t = gamma + delta\right)\right) \land \left(\operatorname{Integrable}\left(curvature\right) \land \left(\operatorname{integral}\left(t, \operatorname{Real}\left(\right), curvature\left(t\right), \operatorname{volume}\left(\right)\right) = 0 \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; \left|t - gamma\right| < delta \Rightarrow curvature\left(t\right) < 0\right) \land \left(\forall t \in \operatorname{Real}\left(\right),\; delta < \left|t - gamma\right| \Rightarrow 0 < curvature\left(t\right)\right)\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/OffLineCurvatureDipole.off_line_curvature_dipole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The potential is constructed from the two reflected squared-distance logarithms. The curvature is its second derivative in the normal coordinate at zero, rather than an alias for the target formula.

Direct differentiation supplies the rational expression and its sign profile. A decaying rational primitive proves integrability and zero total mass over the real line.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/OffLineCurvatureDipole.off_line_curvature_dipole`
