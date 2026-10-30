# Complex Dual Contractions and the Actual Conformal Shift

## Abstract

Complex Dual Contractions and the Actual Conformal Shift

H is a two-sided inverse of the ORIGINAL complex Gram matrix. u is an arbitrary complex vector with G u=beta. Both finite contractions H beta=u and beta^T H=u^T follow without an additional symmetry assumption on H. The actual original-omega operator equals the original Sugawara mode plus sum_i u_i H_i(m) plus delta(m,0) times one half of u^T G u. Choosing u=H beta supplies this representation without rationality or positivity. These equalities are proved about the action-based moduleL definition.

Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.

**Definition 1.1 (shiftCurrent).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.shiftCurrent`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.shiftCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B_m is the finite sum of u_i times the original unshifted neutral current H_i(m).

**Definition 1.2 (halfNorm).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.halfNorm`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.halfNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant is one half of the finite complex quadratic form u^T G u.

**Theorem 1.3 (inverse dual contractions).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.inverse_dual_contractions`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.inverse_dual_contractions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under H G=G H=1 and G u=beta over Complex, both contractions H beta=u and beta^T H=u^T hold for arbitrary complex u.

**Theorem 1.4 (moduleL shift complex).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_shift_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_shift_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual original-omega L_m equals original sugawaraMode_m+B_m+delta(m,0) halfNorm(u) times identity. G u=beta is the only premise on u.

**Theorem 1.5 (inverse dual vector).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.inverse_dual_vector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.inverse_dual_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original right inverse G H=1 gives G(H beta)=beta, without rationality or positivity.

**Theorem 1.6 (moduleL minus one).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_minus_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_minus_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the original inverse identities, actual L_-1=T_D+B_-1. The sector operator is obtained from original omega by the proved shift formula.

**Theorem 1.7 (moduleL minus one single).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_minus_one_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_minus_one_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On single(gamma,p), actual L_-1 is oscillatorDerivation(p) plus multiplication by the sum of (gamma_i+u_i) X_(i,0), in the same charge sector.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.halfNorm`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.inverse_dual_contractions`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.inverse_dual_vector`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_minus_one`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_minus_one_single`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.moduleL_shift_complex`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro.shiftCurrent`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformalShift](LatticeDualCosetConformalShift.md)
