# HsfThreeLevelScalarIdentity

## Abstract

Complex PSD3 cubic geometry and exact scalar coefficients.

**Theorem 1.1 (p396 identity).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact P396 factorization: p396=pqr Q^2(p-q)^2(q-r)^2(r-p)^2 positiveCertificate. The proof uses elementary-symmetric identities and Newton-sum decompositions of the positive certificate.

**Theorem 1.2 (p396 nonneg).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual P396 polynomial is nonnegative for every positive triple, including collisions.

**Theorem 1.3 (p396 pos).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual P396 polynomial is strictly positive at pairwise distinct positive levels.

The statements concern the explicitly defined closed algebraic kernels. The commutant equality classification, identification with the original integrals, dominated differentiation and original HSF derivative/source bridge remain outside these results. No assertion about arbitrary matrix dimension or literature novelty follows.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_pos`
- Dependency: [D5/S3/Quantum/Matrix/HsfThreeLevelScalarCertificate](HsfThreeLevelScalarCertificate.md)
