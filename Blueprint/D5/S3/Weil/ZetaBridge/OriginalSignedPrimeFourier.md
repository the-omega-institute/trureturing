# Original Signed Prime Fourier

## Abstract

The negative actual symmetric von Mangoldt action is expanded on arbitrary finite signed mode sets with arbitrary complex coefficients. Both translations and all prime powers remain. The inclusive q=c row is zero only after compression, including c=5041=71 squared. This component supplies no full Weil positivity or numerical five-mode certificate.

The negative actual symmetric von Mangoldt action is expanded on arbitrary finite signed mode sets with arbitrary complex coefficients. Both translations and all prime powers remain. The inclusive q=c row is zero only after compression, including c=5041=71 squared. This component supplies no full Weil positivity or numerical five-mode certificate.

**Definition 1.1 (head).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.head`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.head` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum ranges over an arbitrary Finset of signed integers, with arbitrary complex coefficients and no even or real restriction.

**Definition 1.2 (primeMatrix).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed matrix is negative the existing primeWeight-weighted sum of the two evaluated complex compression matrices. Every inclusive prime-power row is kept.

**Theorem 1.3 (finite signed prime identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact original primeSymmetric action on the literal zero-extended complex head equals the full double coefficient sum. The actual floor(exp(L)) cutoff is reused, all diagonal and conjugated mixed terms remain, and no matrix identity is an input.

For an integer c>=2 and L=log(c), the original PhysicalCompressedCosineMatrix.primeCutoff at half-window L/2 equals c: unfold primeCutoff, use Real.exp_log for positive c, and take the natural floor of c. Thus c=5040 and c=5041=71 squared give their exact inclusive cutoffs. PhysicalCompressedCosineMatrix.compression_zero_right and compression_zero_left make both shifts at +/-log(c) zero for every profile at the inclusive q=c row. At c=5041 the von Mangoldt weight of 71 squared remains nonzero; it is the compressed row that vanishes.

**Theorem 1.4 (primeMatrix hermitian).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjointness of opposite physical shifts implies Hermiticity of the actual signed finite matrix.

**Theorem 1.5 (finite signed prime real).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_real`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation and exchanging the two finite indices prove reality of the full complex quadratic form. No real-coefficient restriction or positivity conclusion is made.

**Theorem 1.6 (primeMatrix norm le).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual integral entry bounds imply the bound 2*sum(abs(primeWeight(q))) at every finite cutoff.

**Theorem 1.7 (finite signed prime norm le).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-complex quadratic value is bounded by 2*sum(abs(primeWeight(q)))*(sum(norm(v_n))) squared, using actual integral estimates.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_norm_le`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.finite_signed_prime_real`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.head`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix_hermitian`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.primeMatrix_norm_le`
- Dependency: [D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier](OriginalSignedCompressedFourier.md)
