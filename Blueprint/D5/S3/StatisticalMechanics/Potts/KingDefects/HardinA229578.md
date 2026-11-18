# One-defect king colourings: HardinA229578

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (The seven column recurrences).**

$$(\forall (n: \operatorname{Nat}), ((6 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 1\right)\right) = ((((8) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 1\right)\right))) - ((22) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 1\right)\right)))) + ((24) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), 1\right)\right)))) - ((9) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), 1\right)\right)))))) \land ((\forall (n: \operatorname{Nat}), ((3 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 2\right)\right) = ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 2\right)\right))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 2\right)\right)))))) \land ((\forall (n: \operatorname{Nat}), ((5 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 3\right)\right) = ((((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 3\right)\right))) - ((13) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 3\right)\right)))) + ((12) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), 3\right)\right)))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), 3\right)\right)))))) \land ((\forall (n: \operatorname{Nat}), ((7 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 4\right)\right) = ((((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 4\right)\right))) - ((13) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 4\right)\right)))) + ((12) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), 4\right)\right)))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), 4\right)\right)))))) \land ((\forall (n: \operatorname{Nat}), ((7 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 5\right)\right) = ((((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 5\right)\right))) - ((13) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 5\right)\right)))) + ((12) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), 5\right)\right)))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), 5\right)\right)))))) \land ((\forall (n: \operatorname{Nat}), ((7 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 6\right)\right) = ((((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 6\right)\right))) - ((13) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 6\right)\right)))) + ((12) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), 6\right)\right)))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), 6\right)\right)))))) \land (\forall (n: \operatorname{Nat}), ((7 < n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 7\right)\right) = ((((6) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (1), 7\right)\right))) - ((13) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (2), 7\right)\right)))) + ((12) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (3), 7\right)\right)))) - ((4) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left((n) - (4), 7\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229578` (proved) by `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229578","declaration_gid":"D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The seven conjuncts concern columns one through seven, in that order. Each retains its own height threshold. The first column follows from the path formula; the remaining columns follow from their respective fixed-width formulas.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578.result`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229573](HardinA229573.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229574](HardinA229574.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229575](HardinA229575.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229576](HardinA229576.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229577](HardinA229577.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm](KingClosedForm.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath](KingPath.md)
