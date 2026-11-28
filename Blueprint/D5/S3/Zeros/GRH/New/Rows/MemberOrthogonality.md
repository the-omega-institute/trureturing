# Member Orthogonality

## Abstract

Member Orthogonality

Forms killed by θ, the reflection sums and one Hecke polynomial have zero theta periods; comparison forms are orthogonal to them.

**Theorem 1.1 (stdClassSum_inner_productForm_eq_zero).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/MemberOrthogonality.stdClassSum_inner_productForm_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/MemberOrthogonality.stdClassSum_inner_productForm_eq_zero` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let O satisfy FitsParams, ψ ≠ 1 on Q, 2|r| + 2|N| + 3 < |n|, M² = (ϖ), and Ξ killed by θ, the reflection sums and one Hecke polynomial at AuxPair.testValue. Then the level-ϖ class sum over h of ⟨DividedSplitting.productForm(x, h)(y, conj kernelVector(g, h)), Ξ⟩ vanishes.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/MemberOrthogonality.stdClassSum_inner_productForm_eq_zero`
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/PeriodVanishing](../../Lib/Shimura/ComplexTheta/PeriodVanishing.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/MonomialCoefficientVector](MonomialCoefficientVector.md)
