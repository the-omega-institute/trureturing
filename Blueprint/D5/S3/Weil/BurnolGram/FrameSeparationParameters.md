# Frame Separation Parameters

## Abstract

Finite frame geometry supplies the radius and positive squared gaps needed by the sparse negative Weil certificate.

**Theorem 1.1 (Every frame admits separation parameters).**

Lean statement: `D5/S3/Weil/BurnolGram/FrameSeparationParameters.exists_frame_separation_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/FrameSeparationParameters.exists_frame_separation_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of node norms bounds every node. Injectivity of nodeEquiv and the stored signSeparated field exclude equal squares for distinct labels in all four plus/minus combinations. The exception set removes every selected four-point orbit, so injectivity of gamma and its reflection and conjugation identities exclude target-to-exception square collisions. Finite positive minima choose the nodal gap first and the exception gap afterward; empty sets use one.

**Theorem 1.2 (The full certificate with only arithmetic premises).**

Lean statement: `D5/S3/Weil/BurnolGram/FrameSeparationParameters.exists_arithmetic_sparse_negative_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/FrameSeparationParameters.exists_arithmetic_sparse_negative_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the radius and both gaps before the arithmetic inputs. The existing finite-data theorem then gives positive definiteness of the negative full Gram matrix, exact negative index, the original support bound and the original quadratic margin at every depth above the rational threshold. The cutoff comparison, budget comparison and integer conditions remain premises. The theorem assumes a frame and does not assert a nonempty off-line frame exists.

## References

- Truth anchor: `D5/S3/Weil/BurnolGram/FrameSeparationParameters.exists_arithmetic_sparse_negative_certificate`
- Truth anchor: `D5/S3/Weil/BurnolGram/FrameSeparationParameters.exists_frame_separation_parameters`
- Dependency: [D5/S3/Weil/BurnolGram/WeilFiniteDataNegativeCertificate](WeilFiniteDataNegativeCertificate.md)
