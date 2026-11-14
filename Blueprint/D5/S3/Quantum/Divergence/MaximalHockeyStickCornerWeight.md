# The original sum is faithful on the normalized common interior

## Abstract

The original sum is faithful on the normalized common interior

The positive-definite conclusion is about the compressed space, not ambient invertibility. It remains valid on an empty interior. This bridges singular original pairs to the faithful weighted criterion.

**Definition 1.1 (InteriorIndex).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.InteriorIndex`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.InteriorIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

InteriorIndex hC is the subtype of eigenvalue indices with 0<lambda_i<1. It is the domain of the actual rectangular eigenvector embedding.

**Definition 1.2 (interiorEmbedding).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.interiorEmbedding`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.interiorEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

interiorEmbedding hC consists of the eigenvector-unitary columns indexed by InteriorIndex hC. The weight and diagonal spectral coordinate statements use this physical embedding.

**Theorem 1.3 (embedding isometry).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.embedding_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.embedding_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

The adjoint of the interior eigenvector embedding times the embedding is the subtype identity. compressed_weight_posDef uses injectivity supplied by this isometry.

**Theorem 1.4 (embedding eigenvectors).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.embedding_eigenvectors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.embedding_eigenvectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

C times the interior embedding equals the embedding times the diagonal matrix of its interior eigenvalues. This relation excludes kernel vectors when proving faithful compression.

**Theorem 1.5 (compressed weight posDef).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.compressed_weight_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.compressed_weight_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD S and Hermitian C with spectralSupport(S) C=C, the compression J* S J to the eigenvalues 0<lambda(C)<1 is positive definite. No ambient faithfulness of S is assumed. original_pair_weight_posDef consumes this support argument.

**Theorem 1.6 (original pair weight posDef).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.original_pair_weight_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.original_pair_weight_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every PSD A,B, C=normalize(A+B,A) has interior embedding J with J*(A+B)J positive definite, including the zero pair and empty corner. OriginalPair uses this exact result to discharge the only faithfulness hypothesis in the common-corner criterion.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.InteriorIndex`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.compressed_weight_posDef`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.embedding_eigenvectors`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.embedding_isometry`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.interiorEmbedding`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.original_pair_weight_posDef`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickCorner](MaximalHockeyStickCorner.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickSupport](MaximalHockeyStickSupport.md)
