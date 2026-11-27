# Vacuum plane wave curvature and causal focusing

## Abstract

A quadratic vacuum plane wave has a quadruple principal null direction, contracts transverse null screens, and increases the volume of an axial causal diamond.

In coordinates (u, v, x, y), the metric is −2 du dv + A(x²−y²) du² + dx² + dy². The opposite transverse curvature components cancel in the Ricci tensor. The circular and hyperbolic transverse solutions give different changes to screen area and diamond volume.

**Theorem 1.1 (Coordinate volume density).**

$$\forall A \in \mathbb{R},\; \forall p \in \operatorname{Point},\; \operatorname{det}\left(\operatorname{metric}\left(A, p\right)\right) = -1$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.metric_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expansion along the first row gives determinant −1 at every coordinate point for every real amplitude. The density of the metric volume in these coordinates is therefore one.

**Theorem 1.2 (Vacuum Ricci tensor).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.ricci_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.ricci_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate connection is obtained by differentiating the metric and contracting with its inverse. The antisymmetrized quadratic connection terms cancel. The lowered curvature is the difference of the squares of du∧dy and du∧dx, each weighted by A. In the Ricci trace the only surviving candidates have both free indices along u and contribute −A and A.

**Theorem 1.3 (Curvature in the orthonormal pair basis).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.waveWeyl_pairMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.waveWeyl_pairMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pulling back the coordinate curvature to the oriented orthonormal frame gives electric block diag(−A/2,A/2,0), equal mixed blocks with off-diagonal entries A/2 in positions (1,2) and (2,1), and spatial block equal to the negative electric block.

**Theorem 1.4 (Exact Weyl quartic).**

$$\forall A \in \mathbb{R},\; \operatorname{weylQuarticEquiv}\left(\operatorname{waveWeyl}\left(A\right)\right) = \operatorname{C}\left(-4 \cdot A\right) \cdot \operatorname{X}^{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.wave_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate the imported Weyl quartic on the complex null screens. In the oriented pair basis the two wedge blocks differ by the scalar −i. Expanding the resulting quadratic form gives −4AZ⁴. Agreement at every complex Z gives polynomial equality.

**Theorem 1.5 (Quadruple propagation ray).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.wave_typeN`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.wave_typeN` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero A the polynomial has the single finite zero Z=0 with multiplicity four and nonzero fourth coefficient. The frame sends this chart generator to √2 times the v coordinate vector.

**Theorem 1.6 (Closed-form affine null geodesic).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.nullGeodesic_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.nullGeodesic_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero frequency ω with A=ω², the x coordinate is x₀ cosh(ωu)+α sinh(ωu)/ω. The y coordinate is y₀ cos(ωu)+β sin(ωu)/ω. The v coordinate changes by half the increment in xx′+yy′. Two differentiations give the affine connection equation, and a single differentiation of v gives zero metric speed.

**Theorem 1.7 (Parallel caustic).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.parallel_first_caustic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.parallel_first_caustic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roger Penrose (1965). *A Remarkable Property of Plane Waves in General Relativity*. DOI: [10.1103/RevModPhys.37.215](https://doi.org/10.1103/RevModPhys.37.215). URL: <https://doi.org/10.1103/RevModPhys.37.215>.

*Commentary.*

For positive ω the determinant of the position Jacobian is positive for 0<u<π/(2ω). At the endpoint the second diagonal entry is zero, while the first is the strictly positive cosh(π/2).

**Theorem 1.8 (Vertex caustic).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.vertex_first_caustic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.vertex_first_caustic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roger Penrose (1965). *A Remarkable Property of Plane Waves in General Relativity*. DOI: [10.1103/RevModPhys.37.215](https://doi.org/10.1103/RevModPhys.37.215). URL: <https://doi.org/10.1103/RevModPhys.37.215>.

*Commentary.*

For positive ω the determinant of the velocity Jacobian is positive for 0<u<π/ω. At the endpoint the second diagonal entry is zero, while the first is the strictly positive sinh(π)/ω.

**Theorem 1.9 (Strict transverse contraction).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.screen_area_contracts`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.screen_area_contracts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parallel determinant lies strictly between zero and one before the parallel caustic. Its second derivative with respect to ωu is −2 sin(ωu)sinh(ωu). The vertex determinant lies strictly between zero and u² before the vertex caustic. The second derivative of t²−sin(t)sinh(t) is 2(1−cos(t)cosh(t)).

**Theorem 1.10 (Leading vertex area correction).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.vertex_area_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.vertex_area_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Taylor coefficients of sin(t)sinh(t) through degree six are those of t²−t⁶/90. On the punctured neighborhood of zero, division by t² gives relative area 1−t⁴/90 with remainder o(t⁴).

**Theorem 1.11 (Strict excess of axial diamond volume).**

Lean statement: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.axial_diamond_volume`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.axial_diamond_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take axial tips (0,0,0,0) and (T,V,0,0), with ω>0, T>0, ωT<π and V>0. The minimum longitudinal increments on the two timelike segments are quadratic in the transverse endpoint. Their sum has coefficients Kx=ω(coth(ωu)+coth(ω(T−u))) and Ky=ω(cot(ωu)+cot(ω(T−u))) in the two directions. Integrating the available longitudinal height V−(Kx x²+Ky y²)/2 over its positive ellipse gives πV²/√(KxKy). Write r(t)=sin(t)sinh(t)/t² with r(0)=1. The logarithm of r is strictly concave before π, so the slice ratio √(r(ωu)r(ω(T−u))/r(ωT)) exceeds one. Integration over u gives a four-volume strictly above the flat value πV²T²/6.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.axial_diamond_volume`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.metric_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.nullGeodesic_spec`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.parallel_first_caustic`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.ricci_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.screen_area_contracts`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.vertex_area_asymptotic`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.vertex_first_caustic`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.waveWeyl_pairMatrix`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.wave_quartic`
- Truth anchor: `D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.wave_typeN`
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
