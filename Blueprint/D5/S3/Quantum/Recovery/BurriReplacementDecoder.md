# A replacement channel and the Schumacher-Westmoreland construction

## Abstract

Actual Appendix A replacement-channel decoders and their strict squared-fidelity comparison.

The input is a qubit with reference density diag(2/3,1/3). The channel output space B has dimension one. The environment is literally A times B', as prescribed in Appendix A of Burri, arXiv:2502.17411v1. The reference purification has correlated amplitudes sqrt(2)/sqrt(3) and 1/sqrt(3). The same unit vector is the fixed R'A' ancilla, and W is the identity. The matrix M retains the transpose in Eq. A.6. These objects address the actual decoder construction; no lower bound is used as a decoder fidelity.

**Theorem 1.1 (Normalized reference vector).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.psi_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.psi_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correlated reference vector has squared norm one.

**Theorem 1.2 (Physical Stinespring isometry).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map from A to B times E is an isometry with E=A times B'. Its environment components are the replacement channel Kraus operators.

**Theorem 1.3 (A unitary on the full source space).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correlated two-dimensional block is [[5,sqrt(2)],[-sqrt(2),5]] divided by 3 sqrt(3). The orthogonal complement is fixed. Both adjoint products are the identity.

**Theorem 1.4 (Exact ordered polar product).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_polar_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_polar_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X=|psi><psi| and the displayed diagonal matrix sqrtQ, set M=(sqrtQ X) transposed. The product M U equals X/sqrt(3). This statement retains the source multiplication order.

**Theorem 1.5 (The actual positive square root of X).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_square_root`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_square_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank-one state X is a projection. Its positive square root in the canonical CStarMatrix functional calculus is X itself.

**Theorem 1.6 (Positivity of the polar product).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_polar_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_polar_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered product M U is positive semidefinite, since it equals the positive multiple X/sqrt(3).

**Theorem 1.7 (Singular value decomposition with the specified source action).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_svd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_svd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are unitary matrices H and T and nonnegative real diagonal entries s such that M=H diag(s) T and U=T adjoint H adjoint. Thus the explicit U arises from an SVD with precisely the Appendix A convention. The proof applies the Hermitian spectral theorem to M U.

**Theorem 1.8 (The purification identity with a fixed ancilla).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_purification_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_purification_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every reference, environment and purifying index, the canonical positive-root amplitude of X agrees with the physical Stinespring purification tensored with the fixed unit ancilla and acted on by W=I. This is the entrywise identity of Eq. A.9 on the full prescribed spaces.

**Theorem 1.9 (Replacement-channel Kraus normalization).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.noise_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.noise_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram sum of the environment components of V is the input identity.

**Theorem 1.10 (Actual composite decoder columns).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.sw_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.sw_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the source Kraus rows with the ancilla preparation gives two nonzero correlated columns: 2 sqrt(2)/3 and 1/3. These columns are derived from U W and the preparation matrix.

**Theorem 1.11 (Decoder Kraus normalizations).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.decoder_normalizations`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.decoder_normalizations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the composite source decoder Kraus family and the reference-root times noise-adjoint Kraus family have Gram sum equal to the identity of B.

**Theorem 1.12 (Canonical completely positive trace-preserving maps).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_channels`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_channels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the three specified Kraus families is realized by the repository's canonical QuantumChannel interface, with equality of its action and the finite Kraus sum on every input matrix. The following statements identify the physical marginals and ordinary Petz recovery and evaluate the overlap for the actual composite maps.

**Theorem 1.13 (Marginals of the physical Stinespring purification).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.physical_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.physical_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The RBE pure density is constructed from the canonical reference vector and V. Its RE marginal is X, its R marginal is rho, and its E marginal is diag(2/3,1/3) in the full source environment coordinates.

**Theorem 1.14 (Positive reference square root).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.reference_root`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.reference_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The functional-calculus positive square root of rho is the diagonal matrix with entries sqrt(2)/sqrt(3) and 1/sqrt(3).

**Theorem 1.15 (Positive root of the actual product marginals).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.product_marginal_root`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.product_marginal_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed matrix sqrtQ is the unique positive square root of rho tensor sigmaE, where both factors are proved physical marginals.

**Theorem 1.16 (The ordinary Petz channel with zero completion defect).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.ordinary_petz_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.ordinary_petz_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The noise output of rho is the identity on Fin 1 and is positive definite. Its spectral support and inverse positive square root are both the identity. The displayed petzKraus are therefore exactly the ordinary Petz Kraus factors. The reference-state completion theorem supplies the canonical CPTP map, and its complementary reset term vanishes on every input matrix.

**Theorem 1.17 (Canonical purification amplitude).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.canonical_reference_amplitude`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.canonical_reference_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reference vector is entrywise the positive square root of the nonuniform density rho.

**Theorem 1.18 (Normalized canonical reference purification).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.canonical_reference_purification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.canonical_reference_purification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reference vector has squared norm one, its rank-one density is positive semidefinite, and its input marginal is exactly rho.

**Theorem 1.19 (Actual recovered reference-output densities).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_recovered_purifications`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_recovered_purifications` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reference tensor extension of the actual Petz-after-noise channel sends the canonical pure reference density to rho tensor rho. The actual Appendix A SW-after-noise channel sends it to rho tensor diag(8/9,1/9). These identities precede the fidelity calculation.

**Theorem 1.20 (Supported source action is independent of the polar completion).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_supported_action_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_supported_action_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unitary Uprime with M Uprime positive semidefinite, Uprime psi equals U psi. Positive-square-root uniqueness first fixes M Uprime; unitarity then fixes its action on the prepared rank-one source support. Thus arbitrary null-space completion cannot alter the actual replacement decoder Kraus rows.

**Theorem 1.21 (Squared pure-amplitude fidelity for the actual composites).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_composite_squared_overlaps`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_composite_squared_overlaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The overlap of the actual recovered reference density equals the sum of squared pure-state amplitudes of the tensor-lifted composite Kraus operators. The Kraus operators are the products of the actual decoder and physical noise Kraus operators. The equality is proved from the canonical channel action on every input matrix.

**Theorem 1.22 (SW strictly beats ordinary Petz for this physical channel).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_strict_fidelity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_strict_fidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared pure-reference overlap of the actual Petz composite is 1/3, and that of the actual source SW composite is 11/27. Their difference is 2/27, so the SW fidelity is strictly larger. Fidelity is defined by the actual recovered density's overlap with the canonical reference vector, rather than by a reduced target formula. This is the replacement-channel direction of Burri's Question 1 only; the opposite direction and the full no-order conclusion are not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_channels`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_composite_squared_overlaps`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_recovered_purifications`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.actual_strict_fidelity`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.canonical_reference_amplitude`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.canonical_reference_purification`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.decoder_normalizations`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.noise_normalization`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.ordinary_petz_channel`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.physical_marginals`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.product_marginal_root`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.psi_normalized`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.reference_root`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_isometry`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_polar_positive`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_polar_product`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_purification_identity`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_square_root`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_supported_action_unique`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_svd`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.source_unitary`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReplacementDecoder.sw_columns`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Recovery/ReferencePetzChannel](ReferencePetzChannel.md)
