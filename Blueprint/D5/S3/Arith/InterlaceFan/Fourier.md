# Evaluation and closed faces

## Abstract

Cosine coordinates for the interlace fan.

**Theorem 1.1 (Constant certificate values force the zero vector).**

Lean statement: `D5/S3/Arith/InterlaceFan/Fourier.eq_zero_of_I_const`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Fourier.eq_zero_of_I_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least two, if all certificate values of a sigma-coordinate vector equal the same real number, the vector is zero. Augment the coordinates by the constant cosine mode. The cosine nodes at angles between zero and pi are distinct. A Chebyshev expansion of degree at most floor(n/2) that vanishes on all floor(n/2)+1 nodes is the zero polynomial. Linear independence of the Chebyshev sequence then gives injectivity of the augmented evaluation map.

**Theorem 1.2 (Certificate inclusion reverses face inclusion).**

Lean statement: `D5/S3/Arith/InterlaceFan/Fourier.face_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Fourier.face_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If S is contained in T, every vector at which the certificates in T attain the maximum also has this property for the certificates in S. Thus the closed face for T is contained in the closed face for S.

**Theorem 1.3 (Zero weighted mean).**

Lean statement: `D5/S3/Arith/InterlaceFan/Fourier.I_weighted_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Fourier.I_weighted_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of all certificate values, with weight one at zero and at the midpoint for even n and weight two elsewhere, is zero. Reflection pairs the two halves of a full period. The full-period cosine sum vanishes for every positive frequency less than n; the geometric trigonometric sum identity supplies this cancellation.

**Theorem 1.4 (Realization of zero-mean certificate data).**

Lean statement: `D5/S3/Arith/InterlaceFan/Fourier.exists_of_I_values`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Fourier.exists_of_I_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least two, every real family on the certificate indices whose weighted mean is zero is realized by a sigma-coordinate vector. The injective square augmented cosine evaluation map is surjective by finite-dimensional linear algebra. Its weighted mean is n times the constant coordinate, so the given mean condition forces that coordinate to vanish.

**Theorem 1.5 (Exact maximizing certificate sets).**

Lean statement: `D5/S3/Arith/InterlaceFan/Fourier.exists_face_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Fourier.exists_face_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty proper subset S of the certificate indices is exactly the maximizing set of a nonzero vector in its closed face. Subtract the weighted average from the indicator of S, then realize the resulting data. The two resulting levels differ by one. Every index outside S has strictly smaller value than the interlace number. Together with reversal of face inclusion, this gives the face structure used in the rational-point classification.

## References

- Truth anchor: `D5/S3/Arith/InterlaceFan/Fourier.I_weighted_sum`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Fourier.eq_zero_of_I_const`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Fourier.exists_face_exact`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Fourier.exists_of_I_values`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Fourier.face_antitone`
- Dependency: [D5/S3/Arith/InterlaceFan/Defs](Defs.md)
