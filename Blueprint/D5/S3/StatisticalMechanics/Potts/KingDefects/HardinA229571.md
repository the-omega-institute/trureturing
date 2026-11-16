# One-defect king colourings: HardinA229571

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (The square-array recurrence).**

$$\forall (n: \operatorname{Nat}), ((9 \le n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, n\right)\right) = ((((((9) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), (n) - (1)\right)\right))) - ((33) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), (n) - (2)\right)\right)))) + ((63) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), (n) - (3)\right)\right)))) - ((66) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), (n) - (4)\right)\right)))) + ((36) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (5), (n) - (5)\right)\right)))) - ((8) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (6), (n) - (6)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229571.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229571` (proved) by `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229571.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229571","declaration_gid":"D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229571.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *Number of defective 4-colorings of an n X n 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229571>.

*Commentary.*

The six-step integer recurrence holds for every n at least nine. All terms are the literal canonical square-array counts.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229571.result`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm](KingClosedForm.md)
