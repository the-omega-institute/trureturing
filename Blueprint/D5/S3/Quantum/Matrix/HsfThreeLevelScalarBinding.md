# HsfThreeLevelScalarBinding

## Abstract

Complex PSD3 cubic geometry and exact scalar coefficients.

**Theorem 1.1 (scalar p396 margin).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.scalar_p396_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.scalar_p396_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cleared certificate establishes the P396 bound for the actual rho and Xi, with every denominator proved positive.

**Theorem 1.2 (coefficient domination).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.coefficient_domination`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.coefficient_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive triple, actual Xi is at most the Gram allowance of the actual three rho weights. The all-equal case and all other collisions are included.

**Theorem 1.3 (closed cubic nonneg).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.closed_cubic_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.closed_cubic_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all positive p,q,r and every complex PSD three by three S, the actual closed cubic is nonnegative. The statement places no restriction on source rank, complex phases or level collisions.

The statements concern the explicitly defined closed algebraic kernels. The commutant equality classification, identification with the original integrals, dominated differentiation and original HSF derivative/source bridge remain outside these results. No assertion about arbitrary matrix dimension or literature novelty follows.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.closed_cubic_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.coefficient_domination`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.scalar_p396_margin`
- Dependency: [D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity](HsfThreeLevelScalarIdentity.md)
