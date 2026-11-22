# Infima for the earlier examples of the sphere question

## Abstract

Sphere-ratio infima: h = 1 gives 1/√d in dimension d, 0 overall and 1/√2 in dimensions at most two; h(t) = 1/t gives 0.

**Definition 1.1 (The sphere ratio).**

Lean statement: `D5/S3/QuadraticForms/SphereRatioEarlierExamples.ratio`

*Formalization.* `D5/S3/QuadraticForms/SphereRatioEarlierExamples.ratio` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

For h : ℝ → ℝ and x ∈ ℝᵈ, R_h(x) = Σᵢ xᵢ h(xᵢ) / (Σᵢ h(xᵢ)²)^{1/2}.

**Definition 1.2 (Values on active unit vectors).**

Lean statement: `D5/S3/QuadraticForms/SphereRatioEarlierExamples.values`

*Formalization.* `D5/S3/QuadraticForms/SphereRatioEarlierExamples.values` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

The set of values R_h(x) over unit vectors x ∈ ℝᵈ with every coordinate positive: the active-coordinate convention, in which zero coordinates are omitted and d counts the active coordinates.

**Theorem 1.3 (Infima for h = 1 and h(t) = 1/t).**

Lean statement: `D5/S3/QuadraticForms/SphereRatioEarlierExamples.result`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SphereRatioEarlierExamples.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

For h = 1: in every fixed dimension d ≥ 1 the infimum of R_h is 1/√d; in dimension one the only value is 1, and for d ≥ 2 the infimum is not attained. Over all dimensions the infimum is 0 and every value is positive. Over dimensions at most d ≥ 1 the infimum is again 1/√d, and for d ≥ 2 every value exceeds it; for d = 2 this is the infimum 1/√2 over at most two coordinates. For h(t) = 1/t: in every dimension d ≥ 2, in particular already in dimension two, the infimum is 0 and every value is positive.

For h = 1, R_h(x) = (Σᵢ xᵢ)/√d. Each 0 < xᵢ ≤ 1 gives xᵢ² ≤ xᵢ, so Σᵢ xᵢ ≥ 1, strictly when d ≥ 2 because then some xᵢ < 1. Vectors with one coordinate (1 − (d − 1)ε²)^{1/2} and d − 1 coordinates ε give R_h → 1/√d as ε → 0; choosing d large then gives the all-dimension infimum 0. Over dimensions e ≤ d the bound 1/√e ≥ 1/√d applies, and dimension one gives the value 1 > 1/√d when d ≥ 2. For h(t) = 1/t, R_h(x) = d/(Σᵢ xᵢ⁻²)^{1/2} ≤ d√p when one squared coordinate is p, and p → 0 drives the ratio to 0. This is Corollary 10 of H. Ma and W. Zhang (DOI 10.5281/zenodo.23920598). The example h = 1 was suggested by daw (comment 11110291) and h(t) = 1/t was used by Exodd (answer 5146715) on Lucid's sphere question, Mathematics Stack Exchange 5146381, linked from MathOverflow 513954, revision 2.

## References

- Truth anchor: `D5/S3/QuadraticForms/SphereRatioEarlierExamples.ratio`
- Truth anchor: `D5/S3/QuadraticForms/SphereRatioEarlierExamples.result`
- Truth anchor: `D5/S3/QuadraticForms/SphereRatioEarlierExamples.values`
