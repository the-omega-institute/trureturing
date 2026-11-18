# Reference transport for conditional Umegaki divergence

## Abstract

Partial trace, amplification and trace pairing for the actual finite channel action.

**Theorem 1.1 (Faithfulness under partial trace).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z on a finite reference times a nonempty finite local carrier, the ordinary partial trace is positive definite. It is the sum of positive definite principal blocks. The reference center, residual identity and faithful state pairs use this fact.

**Theorem 1.2 (Right reference multiplication under partial trace).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_mul_embed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_mul_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex matrices Z and X, the partial trace of Z times X tensor I is P(Z) times X. This puts the endpoint direction in the kernel and transports the marginal arithmetic operator.

**Theorem 1.3 (Left reference multiplication under partial trace).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_embed_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_embed_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partial trace of (X tensor I) times Z is X times P(Z). This supplies the trace pairing and the left part of the marginal arithmetic operator.

**Theorem 1.4 (Complex trace adjunction).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.trace_embed_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.trace_embed_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tr((X tensor I) adjoint V) equals Tr(X adjoint P(V)) for arbitrary complex matrices, using the ordinary partial trace. This preserves the pairing on zero-partial-trace directions when the reference center is subtracted.

**Theorem 1.5 (Amplification on an elementary tensor).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_kronecker`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_kronecker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite channel N and arbitrary complex X and Z on the reference and input, the amplification sends X tensor Z to X tensor N(Z). This computes the channel image of the identity in the positivity argument.

**Theorem 1.6 (Amplification preserves matrix order).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the canonical finite channel, input matrix order X ≤ Z implies the same order for their amplified images. This transports a strictly positive lower bound.

**Theorem 1.7 (Positive lower bound by the identity).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.positive_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.positive_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive definite complex matrix on a finite carrier dominates m times the identity for some real m > 0. On the empty carrier the proof chooses m = 1. Amplification uses this lower bound.

**Theorem 1.8 (Faithfulness under amplification).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If N(I) is positive definite, the amplified channel sends each positive definite joint Z to a positive definite matrix for every finite reference. The assertion includes correlated input and the empty reference. The inverse-form and density-state proofs use this implication.

**Theorem 1.9 (Right reference multiplication under amplification).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mul_embed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mul_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The amplification of Z times X tensor input identity equals the amplification of Z times X tensor output identity. The reference center and the output residual use this law on arbitrary complex matrices.

**Theorem 1.10 (Left reference multiplication under amplification).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_embed_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_embed_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The amplification of (X tensor input identity) times Z equals (X tensor output identity) times the amplification of Z. This supplies the other multiplication law for the output residual.

**Theorem 1.11 (Bilinear trace pairing of the channel adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_trace_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_trace_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty input and output, every finite reference and arbitrary complex Y and Z, Tr(PhiR(Y) Z) equals Tr(Y amp(N,Z)). The canonical Kraus adjoint is paired with the actual channel action. This gives the channel energy defect and the conjugate-transpose pairing.

**Theorem 1.12 (Hilbert–Schmidt pairing of the channel adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_hs_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_hs_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same carrier hypotheses, Tr(PhiR(Y) adjoint Z) equals Tr(Y adjoint amp(N,Z)). This pairs the chosen output inverse direction and its reference-centered form with the original input direction.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_hs_pair`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.PhiR_trace_pair`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_embed_mul`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_kronecker`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mono`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_mul_embed`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.amp_posDef`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_embed_mul`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_mul_embed`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.partialTraceRight_posDef`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.positive_floor`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiReferenceTransport.trace_embed_pair`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiConditionalKernel](UmegakiConditionalKernel.md)
- Dependency: [D5/S3/Quantum/Divergence/UniversalPositiveScalarizer](UniversalPositiveScalarizer.md)
