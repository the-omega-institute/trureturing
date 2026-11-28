# Clifford and Plücker coordinates for the rank-two cut

## Abstract

Oriented real two-planes give Plücker coordinates for the complex two-mode CAR rank-two cut.

Use the two-mode tracial CAR setting of Wu v1, Remark 3.15. In the ordered occupation basis (00, 01, 10, 11), let L = |0⟩⟨1| and Z = diag(1, −1). Mode 0 is the right mode with lowering jump J₀ = Z ⊗ L. Mode 1 is the left mode with J₁ = L ⊗ I. These are −modeJump 1 and modeJump 0 in the repository, respectively.

**Theorem 1.1 (Coordinates of a complex rank-two projection).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.rank_two_projection_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.rank_two_projection_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For a complex Hermitian idempotent P of rank two, the traceless involution K = 2P − I expands in the fifteen Hermitian Clifford letters Bₖ with real coefficients pₖ = coordinates(K)ₖ. The squared norm ∑ₖ pₖ² is one and all fifteen Plücker relations vanish.

**Theorem 1.2 (Realizing the coordinates by a projection).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.projection_of_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.projection_of_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Conversely, every real unit solution p of the Plücker relations gives a complex Hermitian idempotent P = (I + expand(p))/2 of rank two. Its involution is expand(p) = ∑ₖ pₖ Bₖ.

**Theorem 1.3 (Oriented real two-planes).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.unit_pluecker_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.unit_pluecker_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

A real array p has squared norm one and satisfies all the Plücker relations exactly when p = u ∧ v for an ordered orthonormal pair in ℝ⁶. Its entries are the signed two-by-two minors uᵢvⱼ − uⱼvᵢ. Together with the converse projection construction, this realizes every oriented real two-plane as coordinates of a complex rank-two projection.

**Theorem 1.4 (Per-mode quadratic cut weight).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.within_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.within_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For either lowering jump Jⱼ, let Wⱼ = Re Tr(P Jⱼ P Jⱼ†) be the weight within the range of P. The theorem gives 2(1 − Wⱼ) = ∑ₖ modeDegree(j,k) pₖ². For the cut between P and I − P, the two directed lowering weights sum to 2(1 − Wⱼ), since Jⱼ†Jⱼ + JⱼJⱼ† = I and Tr(P) = 2.

The signed occupation is Sⱼ = I − 2Jⱼ†Jⱼ, with sign +1 on an empty mode and −1 on an occupied mode. Write qⱼ = Re Tr((2P − I) Sⱼ)/4. It equals coordinate p₀ for the right mode and p₉ for the left mode, the 12 and 34 pairs with one-based vertex labels. The occupied trace Re Tr(P Jⱼ†Jⱼ) is 1 − qⱼ. Subtracting Wⱼ from the occupied and empty traces gives the lowering weights 1 − Wⱼ − qⱼ out of P and 1 − Wⱼ + qⱼ into P, respectively.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.projection_of_coordinates`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.rank_two_projection_certificate`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.unit_pluecker_iff`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker.within_quadratic`
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../Information/Pauli/PauliMatrix.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicThermalBasis](WuCubicThermalBasis.md)
