# Holder

## Abstract

Product Schatten Holder inequality for arbitrary square complex matrices.

**Theorem 1.1 (Every positive exponent).**

$$\forall u: \operatorname{Level}(),\ d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ A, B: \operatorname{Matrix}(d, d, \mathbb{C}),\ r, p, q: \mathbb{R},\ 0<r\land0<p\land0<q\land\frac{1}{r}=\frac{1}{p}+\frac{1}{q}\implies\ \operatorname{schattenNorm}(AB, r)\le\operatorname{schattenNorm}(A, p)\times\operatorname{schattenNorm}(B, q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/Holder.schattenNorm_mul_le` (`✓ std3`). ∎

*Citation.* Alex Meiburg (2026). *Arbitrary product Schatten Holder inequality in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HermitianMat/Schatten.lean>.

*Commentary.*

For r, p, q positive with 1/r = 1/p + 1/q, the Schatten r norm of AB is at most the product of the Schatten p norm of A and the Schatten q norm of B. The index type is arbitrary finite and decidable; the empty case is included. No Hermitian, positivity, invertibility or commutation assumption is imposed on A or B.

The norm is the real trace of the spectral power p/2 of the Gram matrix A* A, raised to 1/p. The proof bounds singular-value power sums through Horn log-majorization and finite scalar Holder. All real spectral powers are the finite matrix functional calculus.

This is attributed reuse of Alex Meiburg's Apache-2.0 Physlib proof at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142. It supplies the arbitrary-product inequality needed for the inverse-mean trace variational formula; it alone asserts no Hiai joint convexity.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/Holder.schattenNorm_mul_le`
- Dependency: [D5/S3/Quantum/Schatten/PowerMajorization](PowerMajorization.md)
