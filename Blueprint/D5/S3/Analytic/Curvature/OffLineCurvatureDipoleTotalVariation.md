# Off-Line Curvature Dipole Total Variation

## Abstract

The off-line curvature dipole has total variation four divided by its scale.

**Theorem 1.1 (The off-line curvature dipole has exact total variation).**

$$\forall delta, gamma \in \operatorname{Real}\left(\right),\\{}0 < delta \Rightarrow\\{}\operatorname{let} kappa := (t \mapsto 2 \times \frac{(t - gamma)^{2} - (delta)^{2}}{((t - gamma)^{2} + (delta)^{2})^{2}}),\\{}\operatorname{integral}\left(t, \operatorname{Real}\left(\right), \left|kappa\left(t\right)\right|, \operatorname{volume}\left(\right)\right) = \frac{4}{delta}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Curvature/OffLineCurvatureDipoleTotalVariation.off_line_curvature_dipole_total_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen dipole theorem supplies integrability, zero total mass, the negative core, the positive wings, and the boundary zeros. Its elementary primitive gives core mass minus two divided by the scale, so the wings contribute two divided by the scale.

## References

- Truth anchor: `D5/S3/Analytic/Curvature/OffLineCurvatureDipoleTotalVariation.off_line_curvature_dipole_total_variation`
- Dependency: [D5/S3/Analytic/Adelic/OffLineCurvatureDipole](../Adelic/OffLineCurvatureDipole.md)
