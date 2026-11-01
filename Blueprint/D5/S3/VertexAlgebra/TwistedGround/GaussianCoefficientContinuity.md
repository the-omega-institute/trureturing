# GaussianCoefficientContinuity

## Abstract

GaussianCoefficientContinuity

A fixed finite Gaussian occupation coefficient is a finite polynomial in the entries of its kernel.

**Theorem 1.1 (Finite polynomial dependence of ordinary coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity.coefficient_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity.coefficient_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coefficient of Q_K is a finite linear combination of the kernel entries. The finite antidiagonal product formula shows inductively that every coefficient of Q_K^n is continuous in all entries. Multiplication by 1/n! gives continuity of the actual Gaussian coefficient at every finite occupation. No effective-kernel norm bound is needed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity.coefficient_continuous`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate](FactorialFockQuadraticEstimate.md)
