# A Conjugate Quadratic Certificate

## Abstract

The exact quartic certificate splits into conjugate golden-radical quadratics.

**Theorem 1.1 (The two conjugate quadratic factors multiply to the exact quartic).**

$$\forall x \in \mathbb{R},\ q_{+}(x)q_{-}(x)=p(x).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Transcription/ConjugatePolynomialCertificate.conjugate_quadratic_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set q+(x) = x^2 + (-810051203588 + 362265911296 sqrt(5))x + 55406466168660996 - 24778524949233664 sqrt(5), and let q-(x) be its radical conjugate.

Set p(x) = x^4 - 1620102407176 x^3 + 110811693059397656 x^2 + 84768625708978144 x - 246295300782612464. The Lean theorem certifies q+(x)q-(x) = p(x) for every real x.

The proof reuses the pinned Mathlib identity sqrt(5)^2 = 5 and then normalizes the remaining exact ring arithmetic. It asserts only this factorization, not minimality or irreducibility.

## References

- Truth anchor: `D5/S3/Constants/Transcription/ConjugatePolynomialCertificate.conjugate_quadratic_product`
