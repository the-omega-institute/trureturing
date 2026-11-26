# Directed occupation cap and same-spectrum deficit gap

## Abstract

Directed CAR occupation bounds separate a scalar obstruction from the physical cubic deficit.

**Theorem 1.1 (Directed occupation cap).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.jumpWeight_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.jumpWeight_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let x and y be arbitrary complex vectors in the occupation basis 00, 01, 10, 11. Write E, O and F for the empty, odd and full squared coordinate masses. For every t > 0, the sum of the two squared CAR lowering amplitudes from y to x is at most (1+t)E(x)O(y) + (1+1/t)O(x)F(y). The two occupation blocks have Euclidean norms √(E(x)O(y)) and √(O(x)F(y)), so the triangle inequality and Young's inequality give the cap.

**Theorem 1.2 (Forbidden directed edge).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.table_no_unitary_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.table_no_unitary_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The scalar table has rows (1/4, 3/4, 1/2, 0), (1/4, 1/4, 0, 1/2), (0, 0, 1/4, 3/4), and (0, 0, 1/4, 1/4). No complex unitary frame realizes this table with even occupation 1/2 in every column. The row minus column totals fix the empty mass of column 0 at 1/2 and the full mass of column 1 at 1/4. With t = 2/3 the cap gives w₀₁ ≤ 35/48, whereas the table has w₀₁ = 3/4.

**Theorem 1.3 (Negative scalar deficit).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.strengthenedRelaxation_refuted`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.strengthenedRelaxation_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Fix the ascending spectrum λ = (43³, 45³, 73³, 76³)/998625 and h = 3 log(21/20). The table satisfies the scalar CAR constraints at even occupations eᵢ = 1/2 and moment m = (λ₃−λ₀)/2. It also satisfies |∑ⱼ(wᵢⱼ−wⱼᵢ)| ≤ 2eᵢ for every i. Its normalized cubic deficit, (4 cosh(h)/9)(E₃−α₃ H), is strictly below −1/250, with the ordinary Wu cubic coefficient α₃ and entropy H = ∑ᵢ λᵢ log(4λᵢ) + 2 log(cosh h) − 2hm.

**Theorem 1.4 (Positive physical deficit at the same spectrum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.balancedFrame_normalizedCubicDeficit_gt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.balancedFrame_normalizedCubicDeficit_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

At the same λ and h, every complex unitary frame with even occupation 1/2 in each column has normalized cubic deficit strictly greater than 1/500. Here m is the λ-weighted full minus empty mass of its columns. The directed cap bounds the cheapest of the three matching weights, and rational logarithm bounds give the strict margin.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.balancedFrame_normalizedCubicDeficit_gt`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.jumpWeight_le`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.strengthenedRelaxation_refuted`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.table_no_unitary_realization`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicSpectralCertificate](WuCubicSpectralCertificate.md)
