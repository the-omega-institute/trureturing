# Rank-four extremal ray estimates

## Abstract

The exact rank-four extremal rays yield simultaneous bounds on the four complementary nonzero rows and the total mass on those rows.

**Definition 1.1 (Joint reference estimates).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference.RankFourReference`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference.RankFourReference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write σ = √((5 + √5)/10) and b = √((3 − √5)/10). For a critical four-row mask, the difference of its Born masses on two unit states equals 1 + σ − dx − dy for nonnegative spectral deficits dx and dy. The phase-aligned distances rx and ry satisfy (σ − b)rx² ≤ 2dx and (1 − σ)ry² ≤ 2dy. The complementary tail has total first-state square-root mass at least √(1 − σ) − √2 rx. On each tail row, the first-state amplitude norm is at most √(1 − σ)/2 + rx and the second-state amplitude norm is at least √(2/(7 + √5)) − ry.

**Theorem 1.2 (The reference estimates for every affine critical four-row mask).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference.rankFourReference_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference.rankFourReference_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The centered mask selects the pair {2,3} in both bases and the tail consists of {1,4} in both bases. The top and kernel reference rays are obtained from the orthonormal eigenbasis. On each tail row their Born probabilities are respectively (1 − σ)/4 and 2/(7 + √5). The spectral gaps bound the errors after phase alignment, and the two-basis measurement operator bounds the total tail amplitude error by √2 times the state error. The affine state isometry carries these estimates to every transported mask by preserving the row amplitude norms.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference.RankFourReference`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference.rankFourReference_affine`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry](FourierGeometry.md)
