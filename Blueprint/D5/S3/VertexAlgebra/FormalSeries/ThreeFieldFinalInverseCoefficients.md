# Coefficients of the native inverse

## Abstract

Coefficients of the native inverse

**Theorem 1.1 (inverse_coefficients).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalInverseCoefficients.inverse_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalInverseCoefficients.inverse_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative complex algebra R, every generally infinite three-variable formal series P, all natural k and a, and every native index n, the coefficient at (n0,n1,n2) of chartUnit inverse times nativeChart P equals laurentCoefficient P k a at decode k a n. Sorted and unsorted n are included. Legal PowerSeries substitutions at X, Y+XY and Y identify the three inverse factors. The middle coefficient is binom(-a0,q) choose(q,h). A finite antidiagonal reindexing retains both guards j+h<=n0 and q+l<=n1; terms outside the admissible fiber vanish by the binomial choose coefficient or by the unsorted chart branch.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalInverseCoefficients.inverse_coefficients`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone](ThreeFieldFinalCone.md)
