# Canonical purification with the correct complex-state marginal

## Abstract

Positive-root purification and one reference-first entanglement fidelity.

**Definition 1.1 (Squared pure-reference fidelity).**

Lean statement: `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.fidelity`

*Formalization.* `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.fidelity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In reference-first coordinates (r,i), let v(r,i) = (sqrt(rho))(i,r), where sqrt(rho) is the positive functional-calculus square root. Let P = |v><v|. For a genuine QuantumChannel C, apply C to each reference-indexed matrix block of P. The fidelity is Re <v|(id tensor C)(P)|v>. This is squared Uhlmann fidelity against a pure state, with no additional square, square root, or output normalization. The matrix argument is used on the positive trace-one domain certified below.

**Theorem 1.2 (A density with input marginal rho).**

Lean statement: `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.canonical_purification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.canonical_purification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite complex positive semidefinite rho of trace one, P is positive semidefinite, has trace one, and tracing the reference factor gives rho. The proof identifies that partial trace with sqrt(rho) sqrt(rho)-adjoint and uses positivity and positive-root square laws from pinned Mathlib. The input index is the row of the square root; this orientation remains correct for non-real Hermitian states. The eigenbasis purification supplied by the separately attributed physlib port FiniteDensityPurification is not silently identified with this root vector.

**Theorem 1.3 (Exact tensor-factor relabeling).**

Lean statement: `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.overlap_factor_flip`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.overlap_factor_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every vector v and matrix T, swapping both factors in v and both row and column factors in T leaves the complex overlap unchanged. Two finite-sum changes of variables prove the equality. The Burri comparison consumes this lemma to connect the channel-first reverse calculation to the common reference-first quantity.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.canonical_purification`
- Truth anchor: `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.fidelity`
- Truth anchor: `D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.overlap_factor_flip`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/ReferencePetzChannel](ReferencePetzChannel.md)
