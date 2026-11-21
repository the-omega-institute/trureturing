# The reflecting heat Gramian upper bound

## Abstract

The centered inverse of the reflecting heat interpolant gives an upper bound on the physical Gramian.

**Theorem 1.1 (Upper bound via a real biorthogonal witness).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatPhysicalGramian.inverse_diagonal_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatPhysicalGramian.inverse_diagonal_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an entire multiplier satisfying the radial half-width and real-axis envelope bounds, divide the centered inverse density by the nonzero value of the interpolant at the target node before taking its real part. Under the affine time change the density is supported on the physical interval of length L/n². The Jacobian and the target first-cell weight normalize its moments to the Kronecker delta across all positive modes.

The physical L² norm is bounded by the angular real-axis L² norm of the interpolant times n exp(q_j L/2) divided by the target first-cell weight, the modulus of the target nodal value, and sqrt(2π). The time change contributes n and the conversion from angular frequency to cycles contributes 1/sqrt(2π).

The synthesis of the inverse Gramian column has squared norm equal to the target inverse diagonal. Its inner product with the witness equals the same diagonal by the moment equations. Cauchy–Schwarz bounds the square root of the diagonal by the norm of the witness.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatPhysicalGramian.inverse_diagonal_upper_bound`
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatInverseSupport](ReflectingHeatInverseSupport.md)
