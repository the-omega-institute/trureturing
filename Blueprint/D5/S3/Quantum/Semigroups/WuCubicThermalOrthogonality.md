# Thermal charge pairing and direction weights

## Abstract

The Gibbs square-root trace pairing is diagonal on the sixteen physical Wu thermal directions.

**Theorem 1.1 (Gibbs square-root pairing in the G normalization).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_eq_trace_G`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_eq_trace_G` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The source pairing is Tr(S Xᴴ S Y), with S = CFC.sqrt(D r), so it is conjugate-linear in X and linear in Y. For r ≥ 1, the positive diagonal matrix G satisfies G⁶ = D, and the theorem identifies S with G³. The same pairing is therefore the trace of G³ Xᴴ G³ Y, which is the normalization used by the downstream translation-energy calculation.

**Theorem 1.2 (Exact orthogonality and charge-resolved weights).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For a local label in the order identity, lowering E₀₁, raising E₁₀, centered population, the one-mode Gibbs occupations are a = 1/(1 + r³) and b = r³a. The local squared pairing weights are [1, √(ab), √(ab), ab]. A two-mode direction indexed by k = (p,q) is the parity-twisted product of the two local vectors, and its squared weight is the product of the two local weights.

The local signed charges are 0, −1, 1, 0. The parity phase in the second tensor factor is real and squares to one, so for every r ≥ 0 the pairing of two physical directions vanishes when their two labels differ and equals the product weight directionNormSq r k when the labels agree. The statement includes the endpoint r = 0.

**Theorem 1.3 (Diagonal coordinate expansion).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every r ≥ 0 and arbitrary complex matrices X and Y, expand each matrix in the sixteen directions with the explicit coefficient function from WuCubicThermalBasis. Sesquilinearity in the two arguments and the direction orthogonality give the exact sum of conjugate X-coordinates times Y-coordinates, each multiplied by its two-mode Gibbs weight directionNormSq r k.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_direction`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_eq_trace_G`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.gibbsPairing_expansion`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicThermalBasis](WuCubicThermalBasis.md)
