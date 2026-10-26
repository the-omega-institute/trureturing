# ActualChannelAlgebra

## Abstract

These declarations are consumed helpers for the original whole ST37 theorem. They organize the actual channel algebra and reuse the existing pointwise theorem; they are not independent claims of new mathematical content.

**Theorem 1.1 (inputChoi index swap).**

Lean statement: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_index_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_index_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The input-first Choi matrix is exactly the standard Choi matrix pulled back along the swap of its product indices. This identifies the convention used by the original ST37 channel and the pinned complete-positivity API.

**Theorem 1.2 (inputChoi posSemidef).**

Lean statement: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Complete positivity of the actual complex matrix map makes its input-first Choi matrix positive semidefinite. The proof transports the existing Choi positivity criterion through the product-index equivalence.

**Theorem 1.3 (kraus normalization from actual trace).**

Lean statement: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.kraus_normalization_from_actual_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ActualChannelAlgebra.kraus_normalization_from_actual_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

For an arbitrary finite rectangular Kraus family, trace preservation on every complex input matrix implies that the sum of the adjoint Gram matrices is the identity. Evaluation on every complex matrix unit determines every entry of this normalization.

**Theorem 1.4 (actual sqrt columns kraus).**

Lean statement: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_sqrt_columns_kraus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_sqrt_columns_kraus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The actual CFC square root of the input-first Choi matrix is reshaped column by column. Its specified rectangular columns reconstruct the channel on every complex matrix, and trace preservation gives their adjoint Gram sum equal to the identity. The family is the original redundant family, without selecting a minimal Kraus representation.

**Theorem 1.5 (actual cptp left inverse spectral algebra).**

Lean statement: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_spectral_algebra`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_spectral_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

With only positive input dimension, complete positivity, trace preservation and an actual completely positive trace-preserving left inverse, spectral whitening defines a supported unital star representation. The actual support and inverse square root retain their CFC definitions. The representation commutes with the channel identity value and recovers the original channel after multiplication by that value.

**Theorem 1.6 (actual cptp left inverse syndrome rank).**

Lean statement: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_syndrome_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_syndrome_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

For the actual whitened matrix units, the rank of the distinguished diagonal matrix unit is k when the support rank is k times the positive input dimension. The proof uses the existing pointwise isometric tensor factorization and the finite-dimensional rank formula, retaining all original natural-number cases.

**Theorem 1.7 (actual inputChoi rank).**

Lean statement: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_inputChoi_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_inputChoi_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The actual input-first Choi rank is k under the original reversible-channel hypotheses and support rank k times d. The input-first Choi matrix factors through its distinguished diagonal block N(e_vv), and that same block is a submatrix of the Choi matrix. The block has rank k by whitening and the existing syndrome-rank calculation. Both rank inequalities therefore give equality. This is an actual channel rank identity, not an assumption supplied to the smooth square-root step.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_spectral_algebra`
- Truth anchor: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_syndrome_rank`
- Truth anchor: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_inputChoi_rank`
- Truth anchor: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_sqrt_columns_kraus`
- Truth anchor: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_index_swap`
- Truth anchor: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_posSemidef`
- Truth anchor: `D5/S3/Quantum/Recovery/ActualChannelAlgebra.kraus_normalization_from_actual_trace`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Recovery/PointwiseTensorRecovery](PointwiseTensorRecovery.md)
