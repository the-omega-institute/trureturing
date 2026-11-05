# The actual source construction

## Abstract

The full source SVD and its physically irrelevant null-space freedom.

**Theorem 1.1 (A full nonnegative SVD).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseCompletion.full_source_svd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseCompletion.full_source_svd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The active nonnegative SVD extends to the full source matrix by padding both unitary factors with the identity and all inactive singular values with zero. The source-ordered adjoint product of the two factors is precisely the specified sourceU.

**Theorem 1.2 (The source purification identity).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_purification_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_purification_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed ancillary vector is normalized and W is the actual permutation unitary. Applying W to the physical output with this ancilla gives the full canonical square-root purification of the actual complementary state, as in Appendix A.9.

**Theorem 1.3 (The recovered amplitude convention).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_recovered_amplitude`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_recovered_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual source-row recovery multiplies the canonical amplitude on its right by the transpose of sourceU. The positive right-polar product is M sourceU, with M defined by the transposed product of the two positive roots; these two occurrences of a transpose have distinct roles.

**Theorem 1.4 (Every allowed completion has the same decoder rows).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_decoder_completion_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_decoder_completion_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex coisometry Uprime with M Uprime positive semidefinite, uniqueness of the positive square root first determines M Uprime. Invertibility of the active matrix then determines the action on J. Consequently all Appendix A.11 Kraus rows after the actual ancilla preparation agree with the specified decoder, for every physical input and every environment label. No off-support equality is required.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseCompletion.full_source_svd`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_decoder_completion_independent`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_purification_identity`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseCompletion.source_recovered_amplitude`
- Dependency: [D5/S3/Quantum/Recovery/BurriReverseSource](BurriReverseSource.md)
