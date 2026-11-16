# One-defect king colourings: KingDiagonal

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (Closed diagonal sum).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), ((2 \le N) \Rightarrow ((2 \le M) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingDifference}.\operatorname{N_{D}}\left(N, M\right)\right) = (6) \cdot ((((((2: \operatorname{Int}))^{(N) + (1)}) + (((2: \operatorname{Int}))^{(M) + (1)})) + (((2) \cdot ((\operatorname{Int}.\operatorname{ofNat}\left(N\right)) - (1))) \cdot ((\operatorname{Int}.\operatorname{ofNat}\left(M\right)) - (1)))) - (8))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal.N_D_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

For at least three rows and columns, the diagonal count is the sum of two exponential boundary terms and a bilinear interior term. The displayed arithmetic is in the integers.

**Theorem 1.2 (The diagonal sum for two columns).**

$$\forall (N: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{D}}\left(N, 1\right) = (6) \cdot ((N) \cdot ((2)^{(N) - (1)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal.N_D_two_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

For two columns, the diagonal sum has one free binary word per defect position. The formula includes N=0.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal.N_D_closed`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal.N_D_two_columns`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference](KingDifference.md)
