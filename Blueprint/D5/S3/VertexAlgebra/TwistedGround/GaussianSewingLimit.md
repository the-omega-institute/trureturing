# GaussianSewingLimit

## Abstract

GaussianSewingLimit

Hilbert-Schmidt coordinate tails control the ordered resolvents. The exact padded inverse retains the identity on omitted coordinates, whose mixed-vector contribution tends to zero.

**Theorem 1.1 (HS tails imply the required operator norm limit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.compressed_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.compressed_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two-coordinate Hilbert-Schmidt tails tend to zero. Square-summable-column synthesis bounds the operator norm by the Hilbert-Schmidt size, and equality on the coordinate basis identifies the synthesized operator with the compression error.

**Theorem 1.2 (Only strong coordinate projection convergence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.projection_vector_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.projection_vector_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each actual l2 vector, the coordinate projection is its finite sum of coordinate basis components. The unconditional l2 expansion proves convergence to that vector. There is no operator norm convergence claim for P_F to the identity.

**Theorem 1.3 (Ordered inverse convergence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.resolvent_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.resolvent_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two given strict contraction bounds imply 1-BA is a unit. Apply continuity of Ring.inverse at that genuine unit to the operator norm limits of the compressed B and A. The order BA is preserved.

**Theorem 1.4 (The omitted-coordinate correction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.mixed_complement_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.mixed_complement_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact correction is the bounded bilinear functional r applied to (1-P_F)s. Its limit is zero by the strong convergence on the actual l2 column s. This avoids a false norm limit of P_F-1.

**Theorem 1.5 (Exact complement in the padded inverse).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.padded_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.padded_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite coordinate inclusion J_F and its adjoint satisfy J_F^*J_F=1 and J_F J_F^*=P_F. Embedding the finite inverse and using the two actual strict contraction bounds gives (1-Bbar_F Abar_F)^-1 = (1-P_F)+J_F(1-b_F a_F)^-1 J_F^*. The complement term is retained exactly.

**Theorem 1.6 (The diagonal effective blocks).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.padded_inverse_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.padded_inverse_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by Bbar_F kills the omitted-coordinate complement, giving N_F Bbar_F=J_F(1-b_F a_F)^-1 b_F J_F^*. Swapping A and B supplies the other diagonal block.

**Theorem 1.7 (Native finite matrices and l2 rows).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.bilinear_embedded`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.bilinear_embedded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the finite Euclidean basis and use the true coordinate restriction adjoint. Pairing r against the embedded finite operator applied to s is exactly the finite bilinear matrix sum sum_ij r_i M_ij s_j, without conjugation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.bilinear_embedded`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.compressed_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.mixed_complement_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.padded_inverse`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.padded_inverse_mul`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.projection_vector_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit.resolvent_tendsto`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis](../../Quantum/Analysis/TraceClass/ColumnSynthesis.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/CountableGaussianCutoff](CountableGaussianCutoff.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock](GaussianExternalBlock.md)
