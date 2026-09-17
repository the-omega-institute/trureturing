# Caceres' A308090 gcd-factorial-power primality criterion

## Abstract

Caceres' A308090 gcd-factorial-power condition implies primality.

All variables range over the natural numbers N, including zero. The index is n; a(n) is the A308090 value; exponentiation, addition, and factorial are natural-number operations; gcd is the natural greatest common divisor; and Prime(x) means that x is prime. The constants 0, 1, 2, and 3 are natural numbers, n+1 is the successor of n, 0<n means that n is positive, equality is natural equality, and each arrow is logical implication. The scope is exactly the unsigned OEIS Conjecture sentence for every positive n. The case n=0 is excluded because its hypothesis holds while 1 is not prime. The proof takes a prime divisor q of a composite n+1, observes q<=n so that q divides n!, hence q divides both 2^n and 3^n, hence both 2 and 3, a contradiction.

**Definition 1.1 (The A308090 sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{gcd}\left(\operatorname{gcd}\left(2^{n} + \operatorname{factorial}\left(n\right), 3^{n} + \operatorname{factorial}\left(n\right)\right), n + 1\right)$$

*Formalization.* `D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.a` (`✓ std3`).

*Citation.* Pedro Caceres (2019). *OEIS A308090, gcd(2^n + n!, 3^n + n!, n+1), with the conjectured primality criterion gcd = n+1 implies n+1 prime*. URL: <https://oeis.org/A308090>.

*Commentary.*

The sequence value is the gcd of the two factorial-shifted powers and the successor n+1.

**Theorem 1.2 (Caceres' primality criterion).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((\operatorname{a}\left(n\right) = n + 1) \Rightarrow (\operatorname{Prime}\left(n + 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a308090-caceres-gcd-factorial-power-prime-criterion` (proved) by `D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a308090-caceres-gcd-factorial-power-prime-criterion","declaration_gid":"D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.result","resolution_kind":"proved"} -->

*Citation.* Pedro Caceres (2019). *OEIS A308090, gcd(2^n + n!, 3^n + n!, n+1), with the conjectured primality criterion gcd = n+1 implies n+1 prime*. URL: <https://oeis.org/A308090>.

*Commentary.*

For every positive natural index, equality of a(n) with n+1 implies that n+1 is prime. A prime divisor of a hypothetical composite successor divides n factorial and both shifted powers, hence divides both 2 and 3, which is impossible.

## References

- Truth anchor: `D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.a`
- Truth anchor: `D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.result`
