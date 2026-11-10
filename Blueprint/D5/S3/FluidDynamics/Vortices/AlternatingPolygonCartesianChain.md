# Alternating Polygon Cartesian Chain

## Abstract

Use the exact source radial/tangential vectors v0=(0,1) and v1=(s/(1-m*m/2),0), and rotate them into actual real Cartesian displacements. Canonical inverse-chord sums prove the chain equations. The endpoint is nonzero, and the resulting real linear drift orbit is unbounded, also for the dipole and square.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Definition 1.1 (radial0).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.radial0`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.radial0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The real source eigenvector has zero radial and constant unit tangential component.

**Definition 1.2 (radial1).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.radial1`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.radial1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The real source generalized vector has alternating radial component s/(1-m squared / 2) and zero tangential component.

**Definition 1.3 (cartesian0).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian0`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Apply the existing radial/tangential rotation to the source eigenvector.

**Definition 1.4 (cartesian1).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian1`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Apply the same actual Cartesian rotation to the source generalized vector.

**Theorem 1.5 (cartesian chain).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian_chain`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The exact real Cartesian chain corresponding to v0=(0,1), v1=(s/d,0).

**Theorem 1.6 (cartesian0 ne zero).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian0_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian0_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The rotated real tangential source vector is nonzero.

**Theorem 1.7 (unbounded linear drift).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.unbounded_linear_drift`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.unbounded_linear_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The complete real linearized flow has an unbounded orbit, even in the dipole and square.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian0`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian0_ne_zero`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian1`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.cartesian_chain`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.radial0`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.radial1`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.unbounded_linear_drift`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces](AlternatingPolygonRealSpaces.md)
