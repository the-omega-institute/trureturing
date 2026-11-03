# Granvik's A292273 real-part identity

## Abstract

Granvik's real-part identity for the even-supported signed Mobius function.

Here N includes zero, Z denotes the integers, R the reals and C the complex numbers. The function mu is the standard integer-valued Mobius function ArithmeticFunction.moebius. The symbol i is Complex.I. The maps intToReal and intToComplex are the usual coercions from Z to R and C. The exponent n is a natural number and Re is the real part, valued in R.

**Definition 1.1 (The arithmetic definition).**

$$\forall n \in \mathbb{N},\; ((n \bmod 2 = 1) \Rightarrow (a\left(n\right) = 0)) \land ((n \bmod 2 \ne 1) \Rightarrow (a\left(n\right) = -\mu\left(n\right)))$$

*Formalization.* `D5/S3/Arith/Mobius/GranvikMobiusRealPart.a` (`✓ std3`).

*Citation.* Mats Granvik (2024). *OEIS A292273, real-part formula for the even-supported signed Mobius function*. URL: <https://oeis.org/A292273>.

*Commentary.*

The total function a has domain N and codomain Z. Its two exhaustive clauses use the natural remainder modulo two; zero in these clauses is an integer. At the positive indices of OEIS A292273, odd n gives zero and even n gives minus mu(n). The extension used to define a at zero does not add an index to the theorem's conclusion.

**Theorem 1.2 (The positive-index real-part identity).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\operatorname{intToReal}\left(a\left(n\right)\right) = \Re\left(\operatorname{intToComplex}\left(\mu\left(n\right)\right) \cdot i^{n}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Mobius/GranvikMobiusRealPart.result` (`✓ std3`). ∎

*Resolves.* `Problems/granvik-2024-a292273-real-part` (proved) by `D5/S3/Arith/Mobius/GranvikMobiusRealPart.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"granvik-2024-a292273-real-part","declaration_gid":"D5/S3/Arith/Mobius/GranvikMobiusRealPart.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mats Granvik (2024). *OEIS A292273, real-part formula for the even-supported signed Mobius function*. URL: <https://oeis.org/A292273>.

*Commentary.*

For every positive natural index, with no upper bound, the arithmetic definition equals Re(mu(n) times i to the n). This is precisely Mats Granvik's conjecture in revision 24 of A292273. Reduce the power of i modulo four: residues one and three have zero real part, and residue two gives minus one. In residue zero, four divides n, so n is not squarefree and mu(n) vanishes. The proof directly uses Mathlib's moebius_eq_zero_of_not_squarefree, squarefree_iff_prime_squarefree, prime_two, dvd_of_mod_eq_zero, I_pow_eq_pow_mod, I_sq, I_pow_three and mul_re, followed by arithmetic normalization. These four residue classes partition an arbitrary input; they impose no finite cutoff. The Collatz-trajectory interpretation elsewhere in the entry and termination of Collatz trajectories are outside this statement.

## References

- Truth anchor: `D5/S3/Arith/Mobius/GranvikMobiusRealPart.a`
- Truth anchor: `D5/S3/Arith/Mobius/GranvikMobiusRealPart.result`
