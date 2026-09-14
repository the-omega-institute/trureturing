# Krizek's Next-Prime Product Quadruplet

## Abstract

Krizek's next-prime product has four prime neighbors at offsets two and four exactly when the prime input is three.

**Definition 1.1 (The next-prime function).**

$$\forall q \in \mathrm{Nat},\; nextPrime\left(q\right) = sInf\left(\{x \in \mathrm{Nat} \mid (q + 1 \le x \land Prime\left(x\right))\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.nextPrime` (`✓ std3`).

*Citation.* Harry J. Smith; Jaroslav Krizek (2017). *OEIS A136162, List of prime quadruplets {p, p+2, p+6, p+8}*. URL: <https://oeis.org/A136162>.

*Commentary.*

For each natural q, nextPrime(q) is Mathlib's Nat.find applied to the infinitude of primes. It is the least prime greater than or equal to q+1.

**Definition 1.2 (The next-prime product).**

$$\forall q \in \mathrm{Nat},\; Q\left(q\right) = q \cdot nextPrime\left(q\right)$$

*Formalization.* `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.Q` (`✓ std3`).

*Citation.* Harry J. Smith; Jaroslav Krizek (2017). *OEIS A136162, List of prime quadruplets {p, p+2, p+6, p+8}*. URL: <https://oeis.org/A136162>.

*Commentary.*

For each natural q, Q(q) is the product of q and nextPrime(q).

**Theorem 1.3 (The unique prime input).**

$$\forall q \in \mathrm{Nat},\; Prime\left(q\right) \Rightarrow ((Prime\left(Q\left(q\right) - 4\right) \land \left(Prime\left(Q\left(q\right) - 2\right) \land \left(Prime\left(Q\left(q\right) + 2\right) \land Prime\left(Q\left(q\right) + 4\right)\right)\right)) \Leftrightarrow q = 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a136162-krizek-next-prime-product-quadruplet` (proved) by `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a136162-krizek-next-prime-product-quadruplet","declaration_gid":"D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Harry J. Smith; Jaroslav Krizek (2017). *OEIS A136162, List of prime quadruplets {p, p+2, p+6, p+8}*. URL: <https://oeis.org/A136162>.

*Commentary.*

For a prime q, the four natural numbers Q(q)-4, Q(q)-2, Q(q)+2, and Q(q)+4 are all prime exactly when q=3. Subtraction here is truncated natural-number subtraction. For q at least five, q and nextPrime(q) are nonzero modulo three, so their product has residue one or two; respectively Q(q)+2 or Q(q)-2 is then a multiple of three greater than three. The cases q=2 and q=3 reduce to the explicit values 4 and the prime quadruplet 11, 13, 17, 19.

## References

- Truth anchor: `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.Q`
- Truth anchor: `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.nextPrime`
- Truth anchor: `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.result`
