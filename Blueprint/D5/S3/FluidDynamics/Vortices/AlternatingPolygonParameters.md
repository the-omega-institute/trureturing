# Alternating Polygon Parameters

## Abstract

The genuine domain is the set of collision-free Cartesian configurations. The field uses Cartesian Eqs. (1)-(2), with arbitrary positive b and Omega. The positive radius is sqrt(b/(4 Omega)). Field and Jacobian scaling are derived from these equations. For every N at least three and any positive radius and orientation, equilibrium is equivalent to even N and the specified radius. The odd proof uses tangential readout and total charge one, without assuming an even reflection symmetry.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Theorem 1.1 (Collision freedom under physical rotation).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.collision_free_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.collision_free_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

A common rotation preserves the genuine collision-free domain used when differentiating the actual field.

**Definition 1.2 (CollisionFree).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.CollisionFree`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.CollisionFree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The genuine domain of the Cartesian point-vortex equations.

**Definition 1.3 (field).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Cartesian Eqs. (1)--(2), interpreted on `CollisionFree` configurations.

**Definition 1.4 (jacobian).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.jacobian`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.jacobian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Partial derivatives of the actual field, at the specified configuration.

**Definition 1.5 (radius).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The physical radius is the positive square root of b/(4*Omega).

**Theorem 1.6 (field differentiable at).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_differentiable_at`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_differentiable_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

On collision-free configurations every interaction denominator is nonzero, so the actual field has a Frechet derivative.

**Theorem 1.7 (collision free smul).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.collision_free_smul`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.collision_free_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Multiplication by a nonzero radius preserves and reflects collision freedom.

**Theorem 1.8 (radius pos).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius_pos`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Positive b and Omega give a strictly positive radius.

**Theorem 1.9 (radius sq).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius_sq`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The chosen radius satisfies R squared = b/(4*Omega).

**Theorem 1.10 (normalized field).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.normalized_field`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.normalized_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The parameterized Cartesian field at b=2 and Omega=1/2 equals the existing canonical field.

**Theorem 1.11 (field scaling).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

For nonzero R and b=4*Omega*R squared, the actual field at R*w is 2*Omega*R times the normalized field at w, on its collision-free domain.

**Theorem 1.12 (polygon collision free).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.polygon_collision_free`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.polygon_collision_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The canonical polygon belongs to the genuine domain of the field.

**Theorem 1.13 (normalized differentiable).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.normalized_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.normalized_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Existence of the actual multivariable derivative at every normalized polygon.

**Theorem 1.14 (jacobian scaling).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.jacobian_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.jacobian_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Differentiating the field scaling yields the equality of actual Cartesian Jacobians at every canonical polygon.

**Theorem 1.15 (scaled equilibrium).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.scaled_equilibrium`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.scaled_equilibrium` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Positive physical parameters select a strictly positive equilibrium radius.

**Definition 1.16 (rotate).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.rotate`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.rotate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

A simultaneous physical rotation of all vortex positions.

**Definition 1.17 (regular).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The trap-centered polygon, with arbitrary radius and orientation.

**Theorem 1.18 (field rotation).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_rotation`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Rotational covariance follows from the Cartesian equations and distances.

**Theorem 1.19 (regular collision free).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_collision_free`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_collision_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Every positive-radius regular polygon is collision-free, including odd N.

**Theorem 1.20 (angular readout).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.angular_readout`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.angular_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The tangential Cartesian readout uses only equal nonzero radii and distinct points. It requires no odd-pattern radial cancellation.

**Theorem 1.21 (total charge).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.total_charge`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.total_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The specified alternating pattern has total charge zero for even N and one for odd N.

**Theorem 1.22 (odd nonstationary).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.odd_nonstationary`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.odd_nonstationary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

An odd cyclic charge pattern still defines the Cartesian field. Its positive vortex has nonzero tangential velocity at every positive radius.

**Theorem 1.23 (regular equilibrium iff).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_equilibrium_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_equilibrium_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Sharp actual-field boundary for the specified cyclic charge pattern.

**Theorem 1.24 (regular equilibrium iff radius).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_equilibrium_iff_radius`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_equilibrium_iff_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Positive radii identify the square-root radius without a sign ambiguity.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.CollisionFree`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.angular_readout`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.collision_free_rotate`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.collision_free_smul`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_differentiable_at`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_rotation`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.field_scaling`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.jacobian`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.jacobian_scaling`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.normalized_differentiable`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.normalized_field`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.odd_nonstationary`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.polygon_collision_free`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius_pos`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.radius_sq`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_collision_free`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_equilibrium_iff`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.regular_equilibrium_iff_radius`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.rotate`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.scaled_equilibrium`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.total_charge`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum](AlternatingPolygonSpectrum.md)
