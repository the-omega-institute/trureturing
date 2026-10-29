# Actual Normal-Current Boundary Expansion

## Abstract

Actual Normal-Current Boundary Expansion

The actual current is H_i(m)+beta_i delta(m,0). At conformal index m the normal-product coefficient is m+1. Expanding its two vectorwise finite halves gives the original quadratic coefficient plus beta_j H_i(m), beta_i H_j(m), and beta_i beta_j delta(m,0) times identity. In the negative half the right shift occurs at offset -m-1 for m<0. In the other half the first shift occurs at offset zero and the other at offset m for m>=0. The constant term occurs once at m=0. No ambient translation invariance or auxiliary Gram inverse is used.

Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.

**Theorem 1.1 (normal current shift).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformalShift.normal_current_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformalShift.normal_current_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normal coefficient at m+1 equals its unshifted value plus beta_j H_i(m), beta_i H_j(m), and beta_i beta_j delta(m,0) times identity. All sums are vectorwise finite.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformalShift.normal_current_shift`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal](LatticeDualCosetConformal.md)
