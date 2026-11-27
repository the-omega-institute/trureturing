# Thermal degree and signed modular charge

## Abstract

A complex common eigenbasis for the signed two-mode CAR generator and product Gibbs modular conjugation.

**Theorem 1.1 (Generator eigenvalues).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.generator_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.generator_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

In Wu v1, Remark 3.15, equation (3.54), take exponent three and two equal-cap signed CAR modes with r = exp(β/3). Use the actual generator and Gibbs matrix from WuCubicOperatorBridge. For every real r ≥ 0 the one-mode rates are a = 1/(1 + r³) and b = r³a. In local order I, E₀₁, E₁₀, diag(b,−a), the degrees are 0, 1, 1, 2 and the signed charges are 0, −1, 1, 0.

For each pair k of local indices, the direction Vₖ is the ordinary product of the left family, which includes a parity matrix on the second mode for the two off-diagonal local directions, and the right family. The degree d(k) and charge q(k) are the sums of the corresponding local labels. The actual positive-sign generator sends Vₖ to d(k)Vₖ. In the parity-adjusted tensor coordinates, its two signed dissipators act as the sum of the two local generators; the local degrees follow by the identity a+b=1.

**Theorem 1.2 (Gibbs modular eigenvector equation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.modular_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.modular_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For any real r ≠ 0 and every label k, D(r)Vₖ = (r³)^(q(k)) VₖD(r). The Gibbs matrix is the diagonal product of the two local occupation weights. The parity factors commute with these diagonal weights, so the modular charges add.

**Theorem 1.3 (Actual modular conjugation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.modularLinear_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.modularLinear_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For r > 0 the Gibbs matrix is invertible. The complex-linear map X ↦ D(r)XD(r)⁻¹ sends every Vₖ to (r³)^(q(k))Vₖ. The same directions diagonalize the generator.

**Theorem 1.4 (Expansion in sixteen directions).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For r ≥ 0 and every complex matrix X on the two-mode occupation space, undo the parity factor on the left off-diagonal block and apply the one-mode coefficient formula (aX₀₀+bX₁₁, X₀₁, X₁₀, X₀₀−X₁₁) in each index. The resulting sixteen coefficients give X as their linear combination of the Vₖ. The sixteen directions span a sixteen-dimensional complex matrix space, so the explicit family defines a complex basis. Its coordinates are the stated coefficients.

**Theorem 1.5 (Degree bounds absolute charge).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.abs_charge_le_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.abs_charge_le_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every pair of local labels, the absolute value of the sum of the two signed charges is at most the sum of the two degrees.

**Theorem 1.6 (Physical degree-two Hermitian direction).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.generator_highChargeHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.generator_highChargeHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For r ≥ 0 the difference V₍₁,₁₎ − V₍₂,₂₎ is a degree-two generator eigenvector. The two summands have charges −2 and 2, saturating the absolute-charge bound. Their difference is the sum of the matrix units joining occupations (0,0) and (1,1) in both directions, hence is nonzero and Hermitian.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.abs_charge_le_degree`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.expansion`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.generator_direction`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.generator_highChargeHermitian`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.modularLinear_direction`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalBasis.modular_direction`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicOperatorBridge](WuCubicOperatorBridge.md)
