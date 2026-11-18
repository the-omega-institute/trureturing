# One-defect king colourings: HardinA229575

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (The width-5 recurrence).**

$$\forall (n: \operatorname{Nat}), ((7 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 5\right)\right) = ((((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 5\right)\right))) - ((13) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 5\right)\right)))) + ((12) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), 5\right)\right)))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), 5\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229575.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229575` (proved) by `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229575.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229575","declaration_gid":"D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229575.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *Number of defective 4-colorings of an n X 5 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229575>.

*Commentary.*

The four-step recurrence holds for all natural heights n>7, with the width fixed at 5. Counts are cast to integers before subtraction.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229575.result`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm](KingClosedForm.md)
