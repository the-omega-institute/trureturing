# One-defect king colourings: HardinA229572

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (The width-two recurrence and closed form).**

$$(\forall (n: \operatorname{Nat}), ((3 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 2\right)\right) = ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 2\right)\right))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 2\right)\right)))))) \land (\forall (n: \operatorname{Nat}), ((1 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 2\right)\right) = (((2: \operatorname{Int}))^{(n) - (2)}) \cdot (((7) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right))) - (8)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229572.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *Number of defective 4-colorings of an n X 2 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229572>.

*Commentary.*

The recurrence starts at n>3 and the explicit formula starts at n>1. Both assertions concern the same canonical width-two count.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229572.result`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm](KingClosedForm.md)
