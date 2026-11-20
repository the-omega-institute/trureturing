# The dimension threshold for punctured simplices is sharp

## Abstract

For n = 2 a continuous structured downdate on a once-punctured interval switches its negative index.

**Definition 1.1 (Corollary 6 in dimension two, weak form).**

Lean statement: `D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.claim`

*Formalization.* `D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.claim` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

There is a point c of the open 1-simplex (0, 1) such that every pair of continuous maps d, x from (0, 1) minus c to ℝ² with pivot Δ = xᵀ diag(d) x ≠ 0 and positive semidefinite downdate diag(d) − Δ⁻¹ (diag(d) x)(diag(d) x)ᵀ everywhere has either Δ > 0 everywhere or a fixed index j with dⱼ < 0 everywhere. Each alternative of Corollary 6 implies this disjunction, so Corollary 6 for n = 2 with a one-point deleted set implies the claim.

**Theorem 1.2 (Sharpness of the threshold n ≥ 3).**

Lean statement: `D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

The claim is false: whichever point of (0, 1) is deleted, there are continuous data with nonzero pivot and positive semidefinite downdate whose pivot is not positive everywhere and whose negative diagonal index is not constant. Hence the conclusion of Corollary 6, uniform over finite deleted sets, fails for n = 2, and the threshold n ≥ 3 is sharp.

Delete c. Left of the puncture take D = diag(−1, 1) and x = (1, 0); right of it take D = diag(1, −1) and x = (0, 1). The left piece is open in the punctured interval and so is its complement, so the two-piece maps are continuous. The pivot is −1 on both pieces and the downdates are diag(0, 1) and diag(1, 0), both positive semidefinite. The pivot is negative, so the first alternative fails; the negative diagonal entry is the first coordinate at c/2 and the second at (1 + c)/2, so no index is negative everywhere. This is Corollary 8 of H. Ma and W. Zhang (DOI 10.5281/zenodo.23920598) on MathOverflow 513954, revision 2, asked by Lucid.

## References

- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.result`
- Dependency: [D5/S3/QuadraticForms/StructuredRankOneFamily](StructuredRankOneFamily.md)
