# Gaussian degree majorant

## Abstract

A creation recurrence gives an all-degree Gaussian square-mass bound.

For nonnegative a(n), a(0)=1 and (n+1)a(n+1) <= (c+r*n)a(n), where c>=0 and 0<=r<1, the proofs derive a uniform exponential bound and summability. Neither summability nor a Gaussian norm identity is assumed. The recurrence is supplied by the polynomial creation/derivative estimate in FactorialFockQuadraticEstimate.

**Theorem 1.1 (Uniform bound for every particle cutoff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.partial_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.partial_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N, the sum of a(n) from zero through N is at most exp(c/(1-r)). For the finite polynomial F_N(t), the recurrence gives F_N'(t) <= c/(1-r)*F_N(t) on [0,1]. The integrating factor exp(-c*t/(1-r)) has nonpositive derivative. All sums in this argument are finite.

**Theorem 1.2 (Infinite particle-number summability).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.summable_of_creation_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.summable_of_creation_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform finite partial-sum bound and nonnegativity imply Summable a using the existing Mathlib real series criterion.

**Theorem 1.3 (Bound for the complete series).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.tsum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.tsum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full sum is at most exp(c/(1-r)); no infinite differentiation or interchange is used.

For Gaussian Fock degrees take c=HS(A)^2/2 and r=q^2. This module makes no actual-source/Wick identification, determinant identification or physical realization claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.partial_sum_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.summable_of_creation_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.tsum_bound`
