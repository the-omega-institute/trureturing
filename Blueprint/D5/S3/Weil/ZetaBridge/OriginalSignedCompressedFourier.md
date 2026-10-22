# Original Signed Compressed Fourier

## Abstract

Literal Lebesgue Ioc compression of all signed complex Fourier modes. The interval Fourier calculation is classical, as in Connes--Consani--Moscovici Lemma 2.3 and Section 4. The phase is (-1)^n, the physical interval is (-L/2,L/2], and T_h evaluates x-h. This is only the compressed-translation component; it does not identify the Gamma or full nuX form.

Literal Lebesgue Ioc compression of all signed complex Fourier modes. The interval Fourier calculation is classical, as in Connes--Consani--Moscovici Lemma 2.3 and Section 4. The phase is (-1)^n, the physical interval is (-L/2,L/2], and T_h evaluates x-h. This is only the compressed-translation component; it does not identify the Gamma or full nuX form.

**Definition 1.1 (frequency).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.frequency`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.frequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The frequency is 2*pi*n/L for signed integers n and positive physical length L.

**Definition 1.2 (mode).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.mode`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized profile is exp(i*(2*pi*n/L)*(x+L/2))/sqrt(L). The shifted origin incorporates (-1)^n without changing Lebesgue normalization.

**Definition 1.3 (entry).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conjugate-first physical correlation uses the existing pairing with compression parameter -h. Both inner and outer Ioc indicators are literal.

**Theorem 1.4 (mode continuous).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.mode_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.mode_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This consumed helper supplies continuity of the unextended profile for the finite integral expansion.

**Theorem 1.5 (normalization dictionary).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.normalization_dictionary`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.normalization_dictionary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For L>0 the profile agrees exactly with (-1)^n times the existing OriginalEvenCosineComplete.character at half-length L/2 divided by sqrt(L). Only that exponential character definition is reused, with no even-sector inference.

**Theorem 1.6 (entry nonneg).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<=h<=L direct integration on (h-L/2,L/2] gives the diagonal overlap factor and the guarded off-diagonal exponential quotient. The denominator n-m is used only when m differs from n. Both zero and endpoint shifts are included.

**Theorem 1.7 (pairing line).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.pairing_line`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.pairing_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing compressed pairing equals the line pairing of the two literal zero extensions. This identity is used by both the adjoint calculation and the displacement energy proof.

**Theorem 1.8 (entry adjoint).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A line translation of the original integral yields C_mn(-h)=conj(C_nm(h)) for every real h. No parity of the profiles is assumed.

**Theorem 1.9 (entry disjoint).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Ioc overlap is empty for |h|>=L, including the two touching endpoint shifts. This is proved before any divided difference is used.

**Definition 1.10 (matrix).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.matrix`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.matrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit all-shift complex matrix has separate disjoint, nonnegative-shift and negative-shift branches. Its diagonal and off-diagonal cases remain separate to guard the removable singularity.

**Theorem 1.11 (entry eq matrix).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_eq_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_eq_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual original compressed integral is evaluated by the explicit matrix for every signed pair and every real shift. Positive length is the only length hypothesis.

**Theorem 1.12 (entry paired).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_paired`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_paired` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<=h<=L the diagonal sum is 2*(1-h/L)*cos(w_n*h); for m!=n it is (sin(w_m*h)-sin(w_n*h))/(pi*(n-m)). The result follows by adding the two complex correlations after fixing orientation from their integrals.

**Theorem 1.13 (entry norm le one).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_norm_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_norm_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm is bounded by integrating the constant product amplitude on the literal overlap. The desired contraction is not supplied as an assumption.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_adjoint`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_disjoint`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_eq_matrix`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_nonneg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_norm_le_one`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.entry_paired`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.frequency`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.matrix`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.mode`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.mode_continuous`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.normalization_dictionary`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier.pairing_line`
- Dependency: [D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete](OriginalEvenCosineComplete.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PhysicalCompressedCosineMatrix](PhysicalCompressedCosineMatrix.md)
