# One-defect king colourings: KingClosedForm

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (The canonical count for both side lengths at least four).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), ((4 \le n) \Rightarrow ((4 \le k) \Rightarrow ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, k\right)\right)) = ((((((((((\operatorname{Int}.\operatorname{ofNat}\left(n\right)) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(k\right))) - (\operatorname{Int}.\operatorname{ofNat}\left(n\right))) + ((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(k\right)))) + (12)) \cdot (((2: \operatorname{Int}))^{n})) + ((((((\operatorname{Int}.\operatorname{ofNat}\left(n\right)) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(k\right))) - (\operatorname{Int}.\operatorname{ofNat}\left(k\right))) + ((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right)))) + (12)) \cdot (((2: \operatorname{Int}))^{k}))) + (((16) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right))) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(k\right)))) - ((64) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right)))) - ((64) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(k\right)))) - (32)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The two horizontal-orientation sums and the diagonal sum give the formula after removing colour labels. Every natural count and both dimensions in the polynomial are explicitly cast to integers.

**Theorem 1.2 (The width-two closed form).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 2\right)\right) = (((7) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right))) - (8)) \cdot (((2: \operatorname{Int}))^{(n) - (2)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.width_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The formula holds for every height at least two; subtraction in the exponent is natural subtraction.

**Theorem 1.3 (The width-three closed form).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 3\right)\right)) = (((((3) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right))) + (27)) \cdot (((2: \operatorname{Int}))^{n})) + ((44) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right)))) - (116)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.width_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The heights two and three are included. The general formula follows from the orientation sums.

**Theorem 1.4 (Square arrays).**

$$\forall (n: \operatorname{Nat}), ((3 \le n) \Rightarrow ((2) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, n\right)\right)) = (((((((\operatorname{Int}.\operatorname{ofNat}\left(n\right))^{2}) + ((5) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right)))) + (12)) \cdot (((2: \operatorname{Int}))^{n})) + ((8) \cdot ((\operatorname{Int}.\operatorname{ofNat}\left(n\right))^{2}))) - ((64) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right)))) - (16)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.diagonal_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The square case includes side length three and otherwise specializes the two-dimensional closed form.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.closed_form`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.diagonal_closed`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.width_three`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.width_two`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal](KingDiagonal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts](KingHorizontalCounts.md)
