# Critical Center Coordinate

## Abstract

Critical-center coordinates identify the critical line with the real axis and transport same-height reflection to complex conjugation.

**Definition 1.1 (Critical-center coordinate).**

Lean statement: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.centralCoord`

*Formalization.* `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.centralCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This name reuses the frozen spectral parameter minus i times rho minus one half; it does not introduce a second coordinate source.

**Definition 1.2 (Inverse critical-center coordinate).**

Lean statement: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.invCentralCoord`

*Formalization.* `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.invCentralCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse affine map sends z to one half plus i times z.

**Definition 1.3 (Critical-center coordinate equivalence).**

Lean statement: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.centralCoordEquiv`

*Formalization.* `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.centralCoordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two explicit inverse laws package the coordinate map as an equivalence of the complex plane, so no information is lost.

**Theorem 1.4 (Critical-center coordinate specification).**

$$\forall \rho: \mathbb{C},\\{}\operatorname{Re}(\operatorname{centralCoord}(\rho)) = \operatorname{Im}(\rho) \land \operatorname{Im}(\operatorname{centralCoord}(\rho)) = -{\operatorname{Re}(\rho) - \frac{1}{2}} \land\\{}((\operatorname{Re}(\rho) = \frac{1}{2}) \Leftrightarrow (\operatorname{Im}(\operatorname{centralCoord}(\rho)) = 0)) \land \operatorname{invCentralCoord}(\operatorname{centralCoord}(\rho)) = \rho \land\\{}(\forall z: \mathbb{C}, \operatorname{centralCoord}(\operatorname{invCentralCoord}(z)) = z) \land \operatorname{centralCoord}(1 - \rho) = -\operatorname{centralCoord}(\rho) \land\\{}\operatorname{centralCoord}(\overline{\rho}) = -\overline{\operatorname{centralCoord}(\rho)} \land \operatorname{centralCoord}(\operatorname{reflect}(\rho)) = \overline{\operatorname{centralCoord}(\rho)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.critical_center_coordinate_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real and imaginary component formulas identify the critical line with the real coordinate axis. Both affine inverse laws hold for arbitrary complex points.

Functional reflection acts by negation, conjugation acts by negative conjugation, and their same-height composite acts by ordinary complex conjugation in the new coordinate.

**Theorem 1.5 (One half plus three i has coordinate three).**

$$\operatorname{centralCoord}(\frac{1}{2} + 3i) = 3 \land \operatorname{Re}(\frac{1}{2} + 3i) = \frac{1}{2} \land \operatorname{Im}(\operatorname{centralCoord}(\frac{1}{2} + 3i)) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.critical_line_coordinate_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The on-line witness evaluates the coordinate exactly and has zero coordinate imaginary part.

**Theorem 1.6 (Three quarters plus three i has negative quarter imaginary coordinate).**

$$\operatorname{centralCoord}(\frac{3}{4} + 3i) = 3 - \frac{1}{4}i \land\\{}\operatorname{Re}(\frac{3}{4} + 3i) \neq \frac{1}{2} \land \operatorname{Im}(\operatorname{centralCoord}(\frac{3}{4} + 3i)) = -\frac{1}{4} \land \operatorname{Im}(\operatorname{centralCoord}(\frac{3}{4} + 3i)) \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.off_line_coordinate_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The off-line witness evaluates to three minus one quarter i, verifying the sign and a nonzero coordinate imaginary part.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.centralCoord`
- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.centralCoordEquiv`
- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.critical_center_coordinate_spec`
- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.critical_line_coordinate_witness`
- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.invCentralCoord`
- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.off_line_coordinate_witness`
- Dependency: [D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry](FiniteShiftedBlaschkeSymmetry.md)
