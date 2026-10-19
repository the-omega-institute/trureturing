# Continuity and balanced scalar optimization

## Abstract

Continuity and balanced scalar optimization.

**Theorem 1.1 (Continuity of a matrix norm).**

Lean statement: `D5/S3/Quantum/Schatten/UINormContinuity.continuous_N`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UINormContinuity.continuous_N` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

Every UINorm on complex n by n matrices is continuous in the usual finite-dimensional topology. Subadditivity and absolute homogeneity give convexity, and an everywhere finite convex function on this finite-dimensional real vector space is continuous.

**Theorem 1.2 (Optimization over a positive scale).**

Lean statement: `D5/S3/Quantum/Schatten/UINormContinuity.sq_le_mul_of_balanced_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/UINormContinuity.sq_le_mul_of_balanced_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative real m, f and g, if 2m≤tf+t⁻¹g for every positive real t, then m²≤fg. When m and f are positive, t=m/f suffices; if f=0, a positive scale rules out m>0. Thus the conclusion also includes vanishing factors.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/UINormContinuity.continuous_N`
- Truth anchor: `D5/S3/Quantum/Schatten/UINormContinuity.sq_le_mul_of_balanced_bounds`
- Dependency: [D5/S3/Quantum/Schatten/UnitarilyInvariantNorm](UnitarilyInvariantNorm.md)
