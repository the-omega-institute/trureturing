# Hardin A229635

## Abstract

An order-27 recurrence for the literal width-six array count.

**Theorem 1.1 (The order-27 recurrence).**

$$\forall n: \operatorname{\mathit{Nat}}, ((31 \le n) \implies ((\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n, 6\right): \int) = 54 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 1, 6\right): \int) - 1140 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 2, 6\right): \int) + 11637 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 3, 6\right): \int) - 54252 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 4, 6\right): \int) + 33192 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 5, 6\right): \int) + 658756 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 6, 6\right): \int) - 1921212 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 7, 6\right): \int) - 1566516 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 8, 6\right): \int) + 12850374 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 9, 6\right): \int) - 7108644 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 10, 6\right): \int) - 35018232 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 11, 6\right): \int) + 43506046 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 12, 6\right): \int) + 38500440 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 13, 6\right): \int) - 85687812 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 14, 6\right): \int) - 200796 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 15, 6\right): \int) + 75241308 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 16, 6\right): \int) - 31685592 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 17, 6\right): \int) - 25769200 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 18, 6\right): \int) + 20878068 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 19, 6\right): \int) + 213348 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 20, 6\right): \int) - 3655770 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 21, 6\right): \int) + 608916 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 22, 6\right): \int) + 230904 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 23, 6\right): \int) - 61761 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 24, 6\right): \int) - 2790 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 25, 6\right): \int) + 1800 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 26, 6\right): \int) - 125 \cdot (\operatorname{\mathit{HardinA229637RowColumn}}.\operatorname{T}\left(n - 27, 6\right): \int)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229635` (proved) by `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229635","declaration_gid":"D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result","resolution_kind":"proved"} -->

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The literal count uses maps from the six-column rectangle to three available colours. Each in-range horizontal, diagonal or antidiagonal bond contributes one defect when its colours agree. The filter requires exactly two defects. The first occurrence of each used colour follows row-major order, including colourings that use only two colours.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate](HardinA229635IntegerCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Literal](HardinA229635Literal.md)
