# The Karttunen–Munn conjecture on OEIS A344695

## Abstract

The prime values of gcd of the divisor sum and Dedekind psi are the odd primes.

**Definition 1.1 (Dedekind psi).**

$$\forall n \in \mathbb{N},\; psi\left(n\right) = (\operatorname{Nat}.\operatorname{div}\left(n, \prod_{p \in \operatorname{Nat}.\operatorname{primeFactors}\left(n\right)} (p)\right)) \cdot (\prod_{p \in \operatorname{Nat}.\operatorname{primeFactors}\left(n\right)} (p + 1))$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.psi` (`✓ std3`).

*Citation.* Antti Karttunen; Peter Munn (2021). *OEIS A344695: gcd of the divisor sum and Dedekind psi*. URL: <https://oeis.org/A344695>.

*Commentary.*

OEIS A001615, NAME (unpaginated): "Dedekind psi function: n * Product_{p|n, p prime} (1 + 1/p)." Here n is natural and Nat.primeFactors n is the finite set of distinct prime divisors. Nat.div denotes natural-number integer division, with empty products equal to one. For positive n the product of the prime divisors divides n, giving the displayed integer expression.

**Definition 1.2 (The sequence).**

$$\forall n \in \mathbb{N},\; a\left(n\right) = \operatorname{Nat}.\operatorname{gcd}\left(\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right), psi\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.a` (`✓ std3`).

*Citation.* Antti Karttunen; Peter Munn (2021). *OEIS A344695: gcd of the divisor sum and Dedekind psi*. URL: <https://oeis.org/A344695>.

*Commentary.*

OEIS A344695, NAME (revision 39, unpaginated): "a(n) = gcd(sigma(n), psi(n)), where sigma is the sum of divisors function, A000203, and psi is the Dedekind psi function, A001615." ArithmeticFunction.sigma 1 n is the sum of positive divisors of n. The sequence uses the positive indices n ≥ 1.

**Definition 1.3 (The prime-values conjecture).**

$$claim := (\forall q \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(q\right) \Rightarrow ((\exists n \in \mathbb{N},\; (1 \le n) \land (a\left(n\right) = q)) \Leftrightarrow (Odd\left(q\right))))$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.claim` (`✓ std3`).

*Citation.* Antti Karttunen; Peter Munn (2021). *OEIS A344695: gcd of the divisor sum and Dedekind psi*. URL: <https://oeis.org/A344695>.

*Commentary.*

OEIS A344695, COMMENTS (revision 39, unpaginated): "Conjecture: the set of primes that appear in the sequence is A065091 (the odd primes)." For each natural prime q, appearing means that some natural n ≥ 1 satisfies a n = q. Odd is the natural-number parity predicate.

**Theorem 1.4 (The prime values are exactly the odd primes).**

$$\forall q \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(q\right) \Rightarrow ((\exists n \in \mathbb{N},\; (1 \le n) \land (a\left(n\right) = q)) \Leftrightarrow (Odd\left(q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a344695-gcd-sigma-psi-odd-primes` (proved) by `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a344695-gcd-sigma-psi-odd-primes","declaration_gid":"D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen; Peter Munn (2021). *OEIS A344695: gcd of the divisor sum and Dedekind psi*. URL: <https://oeis.org/A344695>.

*Commentary.*

For a square index, the divisor sum is odd. For a nonsquare index, a prime p of odd exponent makes p + 1 divide both functions, excluding the value 2. For an odd prime q, choose a prime r greater than q² + q + 1 and congruent to 1 modulo q(q + 1)(q² + q + 1). At n = q²r^(q−1), geometric-sum congruences and coprimality give a n = q.

## References

- Truth anchor: `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.a`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.claim`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.psi`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.result`
- Dependency: [D5/S3/Arith/KrizekTriangularSquareSigmaParity](../KrizekTriangularSquareSigmaParity.md)
