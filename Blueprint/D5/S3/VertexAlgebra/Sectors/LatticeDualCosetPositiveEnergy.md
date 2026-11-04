# Actual Original-Omega Energy Eigenspaces

## Abstract

Actual Original-Omega Energy Eigenspaces

beta is integral, mu is rational with G_Q mu=beta, and H is a two-sided inverse of the original complex Gram matrix. The actual moduleL_0 eigenvalue of the unchanged full carrier basis is oscillatorEnergy(d)+q_mu(gamma). Exact duality gives q_mu(gamma)=q_mu(0)+chargeEnergy(gamma)+gamma dot beta. Relative to an attained minimum all basis weights differ by natural numbers. The sealed generic diagonal-tensor coefficient and eigenspace theorems are specialized to the scalar tensor unit; the actual action is retained. Full eigenspaces equal rational coefficient-support grades, and the entire exact fiber supplies their coordinates. Positive original Gram makes them finite dimensional. All statements concern algebraic vectors and point eigenvalues, with no Hilbert completion, analytic spectrum or self-adjointness claim.

Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.

**Theorem 1.1 (chargeWeight expansion).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.chargeWeight_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.chargeWeight_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact rational duality G mu=beta gives q_mu(gamma)=q_mu(0)+chargeEnergy(gamma)+gamma dot beta. Consequently charge-weight differences are integral.

**Theorem 1.2 (weight levels).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.weight_levels`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.weight_levels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a globally minimizing charge gamma_0, every basis weight is q_mu(gamma_0)+n for an actual natural n. Nonnegativity turns the integral difference into a natural number.

**Theorem 1.3 (moduleL basis zero).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_basis_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_basis_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both original inverse equations and exact rational duality, ACTUAL L_0 of original omega acts on every unchanged carrierBasis(gamma,d) by oscillatorEnergy(d)+q_mu(gamma).

**Definition 1.4 (rationalGrade).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.rationalGrade`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.rationalGrade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The grade at rational e is exactly the submodule supported on all actual labels of weight e.

**Theorem 1.5 (moduleL coeff).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary actual v and every label a, coeff(L_0 v,a)=cast(weight(a)) coeff(v,a). The generic diagonal-tensor theorem is used with scalar tensor factor Complex.

**Theorem 1.6 (moduleL eigen iff).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_eigen_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_eigen_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every mixed or homogeneous actual v, L_0 v=cast(e)v if and only if v belongs to the rational coefficient grade at e. Both directions follow from the generic full-eigenspace supplier through the tensor unit.

**Definition 1.7 (gradeCoeffEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.gradeCoeffEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.gradeCoeffEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entire exact rational energy fiber parametrizes the grade by finitely supported complex coefficients, with no positivity needed for this equivalence.

**Theorem 1.8 (eigenspace finiteDimensional).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.eigenspace_finiteDimensional`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.eigenspace_finiteDimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive original Gram makes every actual L_0 eigenspace at a rational eigenvalue finite dimensional via its full exact fiber basis.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.chargeWeight_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.eigenspace_finiteDimensional`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.gradeCoeffEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_basis_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.moduleL_eigen_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.rationalGrade`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy.weight_levels`
- Dependency: [D5/S1/Eigenstructure/DiagonalTensorEigenspace](../../../S1/Eigenstructure/DiagonalTensorEigenspace.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergy](LatticeDualCosetEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro](LatticeDualCosetVirasoro.md)
