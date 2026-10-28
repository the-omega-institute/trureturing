# The finite coprimality convolution

## Abstract

Summing over all prime-power divisors supported on a modulus enforces coprimality.

**Definition 1.1 (Unrestricted prime exponents).**

$$\forall q,n\in\mathbb{N},\operatorname{Supported}\left(q, n\right)\Leftrightarrow \forall p\in\mathbb{N},\operatorname{Prime}\left(p\right)\land \operatorname{Divides}\left(p, n\right)\Rightarrow \operatorname{Divides}\left(p, q\right)$$

*Formalization.* `D5/S3/Arith/MoebiusLogarithmic/CoprimeConvolution.PrimeSupported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Supported(q,n) means that every prime dividing n divides q. No bound is imposed on any exponent in n. The value at n=1 is true, since there are no prime divisors of one.

**Theorem 1.2 (The exact coefficient identity).**

$$\forall q,n\in\mathbb{N},\sum_{d\in \operatorname{divisors}\left(n\right),\operatorname{Supported}\left(q, d\right)}\operatorname{mu}\left(\frac{n}{d}\right) = \operatorname{ite}\left(\operatorname{gcd}\left(n, q\right) = 1, \operatorname{mu}\left(n\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/MoebiusLogarithmic/CoprimeConvolution.sum_supported_moebius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum is over positive divisors d of n whose prime support is contained in that of q. Its coefficient is the actual integer Moebius value mu(n/d). At a prime power p^k, a prime dividing q allows every exponent from zero through k, and Moebius cancellation makes the sum zero when k is positive. For a prime outside q only d=1 remains. Multiplicativity then gives exactly mu(n) on integers coprime to q and zero elsewhere. For n=1 both sides are one. Nat.divisors 0 is empty, and mu(0)=0, so the identity also holds at zero.

## References

- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/CoprimeConvolution.PrimeSupported`
- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/CoprimeConvolution.sum_supported_moebius`
