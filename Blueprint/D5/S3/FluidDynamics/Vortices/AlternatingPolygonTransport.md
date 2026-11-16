# Alternating Polygon Transport

## Abstract

The parameter operator is the complexification of the actual field derivative at the physical radius. Differentiated field scaling identifies it with 2*Omega times the normalized derivative. Every level of every generalized eigenspace is preserved under the corresponding eigenvalue scaling. The characteristic polynomial identity and rescaled neutral chain record the full Jordan transport.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Theorem 1.1 (Actual physical matrix equality).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_matrix_eq`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_matrix_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Differentiate the physical field scaling and map the actual real Cartesian derivative into the complex numbers. This is the matrix identity used by both the operator and characteristic-polynomial transport.

**Theorem 1.2 (smul genEigenspace).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.smul_genEigenspace`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.smul_genEigenspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Scalar dilation preserves every level of the generalized-eigenspace filtration.

**Theorem 1.3 (charpoly smul eval).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.charpoly_smul_eval`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.charpoly_smul_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Determinant scaling, including the zero characteristic root.

**Theorem 1.4 (charpoly smul polynomial).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.charpoly_smul_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.charpoly_smul_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Polynomial, rather than root-list, scaling of an actual square matrix.

**Definition 1.5 (parameterOperator).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameterOperator`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameterOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The physical derivative at the radius selected by b and Omega.

**Theorem 1.6 (parameterOperator eq).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameterOperator_eq`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameterOperator_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The actual complexified physical derivative is exactly 2*Omega times the normalized actual operator.

**Theorem 1.7 (parameter genEigenspace).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_genEigenspace`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_genEigenspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Every eigenvalue and every Jordan filtration level transports from the actual field.

**Theorem 1.8 (parameter charpoly).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

As a polynomial, the actual physical characteristic polynomial is a to the 4m times chi(lambda/a), where a=2*Omega.

**Theorem 1.9 (parameter neutral chain).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_neutral_chain`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_neutral_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The chain length stays two; only the generalized vector is rescaled.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.charpoly_smul_eval`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.charpoly_smul_polynomial`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameterOperator`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameterOperator_eq`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_charpoly`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_genEigenspace`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_matrix_eq`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.parameter_neutral_chain`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.smul_genEigenspace`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative](AlternatingPolygonDerivative.md)
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonNeutral](AlternatingPolygonNeutral.md)
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces](AlternatingPolygonRealSpaces.md)
