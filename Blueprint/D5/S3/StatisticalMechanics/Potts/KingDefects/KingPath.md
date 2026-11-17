# One-defect king colourings: KingPath

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (The width-one count for at least three cells).**

$$\forall (n: \operatorname{Nat}), ((3 \le n) \Rightarrow ((54) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 1\right)\right)) = (((\operatorname{Int}.\operatorname{ofNat}\left(n\right)) - (1)) \cdot (((3: \operatorname{Int}))^{n})) + ((27) \cdot ((\operatorname{Int}.\operatorname{ofNat}\left(n\right)) - (1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.width_one_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A one-column array is a word with exactly one equal adjacent pair. Burnside counting for permutations of four colours gives the formula for every word of length at least three.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.width_one_large`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
