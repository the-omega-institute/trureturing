# Signed Gaussian Candidates

## Abstract

Signed Gaussian Candidates

The signed candidates use the original mode sources and period correction. The normalized source roots are defined through a single complex power on a right half-plane, so their real parts are positive. Their sum cannot vanish. The four rational T denominators follow from the original square-root bidisk bounds.

**Theorem 1.1 (h_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean label and complex u,r with norm(u)+norm(r)<1, the signed source factor h(e,u,r) is nonzero.

**Theorem 1.2 (source_u).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_u`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_u` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative in u of the actual sourceMode(e,u,r) is mLog(e,u,r) times that source, on norm(u)+norm(r)<1.

**Theorem 1.3 (source_frequency).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_frequency`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_frequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero b(u) and h(e,u,r), the original signed first-order source operator has frequency modeA(e,u,r).

**Theorem 1.4 (W_square).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square of W(e,u,r) equals h(e,u,r)/b(u) on the source disk.

**Theorem 1.5 (source_W_normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_W_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_W_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product sourceMode(e,u,r)*b(u)*W(e,u,r) equals one on the source disk.

**Theorem 1.6 (W_sum_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_sum_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_sum_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any labels and complex u,v,r in the two source disks, W(e,u,r)+W(f,v,r) is nonzero. Each normalized root has positive real part.

**Theorem 1.7 (ell_eq_source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.ell_eq_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.ell_eq_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For norm(r)<1, ell(r) is the original shiftedCentralDerivative(r,0) divided by period(r).

**Theorem 1.8 (E_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either pair of labels, E(e,f,u,v,r) is nonzero when norm(u)+sqrt(norm(r))<1 and norm(v)+sqrt(norm(r))<1. These stronger square-root bounds control all four denominators.

**Theorem 1.9 (original_small).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.original_small`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.original_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0<=r<1, norm(w)+sqrt(r)<1 implies norm(w)+norm((r:Complex))<1.

**Theorem 1.10 (candidateT_original_displacement).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0<r<1 on the original source bidisk, the signed T candidate satisfies the exact original spatial displacement equation with original modeA, modeH and central period ratio. All denominator conditions follow from the domain.

**Theorem 1.11 (candidateJ_joint_analytic).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_joint_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_joint_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed J candidate is jointly complex analytic in u,v on the two source disks. Its normalized-root denominator never vanishes, including equal coordinates.

**Theorem 1.12 (candidates_original_joint_differentiable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0<r<1 on the source bidisk, both signed candidates are jointly complex differentiable in u,v, for all four label pairs.

**Theorem 1.13 (candidateJ_diagonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At equal coordinates the signed J candidate is (r/4-correction(r))/(b(u)*h(e,u,r)) plus r squared*u divided by eight times (b(u)*h(e,u,r)) squared. The identity includes u=0.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.E_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_square`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.W_sum_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateJ_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.ell_eq_source`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.h_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.original_small`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_W_normalization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_frequency`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.source_u`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate](../OriginalGaussianExternalAnalyticCandidate.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations](../OriginalGaussianExternalEquations.md)
