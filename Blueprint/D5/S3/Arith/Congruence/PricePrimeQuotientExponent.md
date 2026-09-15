# Price's Prime-Quotient Exponents

## Abstract

A prime quotient (x^k+y^k)/(x+y) for coprime positive bases forces the exponent k to be prime.

**Theorem 1.1 (A prime odd-power quotient has prime exponent).**

$$\forall x \in \mathrm{Nat}, y \in \mathrm{Nat}, k \in \mathrm{Nat},\; ((1 \le y) \land ((y < x) \land ((Coprime\left(x, y\right)) \land ((x + y \mid x^{k} + y^{k}) \land (Prime\left((x^{k} + y^{k}) / (x + y)\right)))))) \Rightarrow (Prime\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.prime_quotient_exponent_is_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert Price (2013). *OEIS A228558, Numbers k such that (17^k + 4^k)/21 is prime*. URL: <https://oeis.org/A228558>.

*Commentary.*

For natural numbers x, y, and k with 1<=y<x and coprime x and y, suppose x+y divides x^k+y^k and the resulting quotient is prime. Then k is prime. Divisibility first forces k to be odd, while k=1 would make the quotient one. If k were odd and composite, a proper divisor d would place x^d+y^d strictly between x+y and x^k+y^k. The two induced quotient factors are nonunits whose product is the asserted prime quotient, a contradiction. This public general-purpose lemma supports both Price specializations and later arguments of the same form. The odd-power factorization supplied by Odd.nat_add_dvd_pow_add_pow is classical Mathlib material.

**Theorem 1.2 (Price's A228558 exponent conjecture).**

$$\forall k \in \mathrm{Nat},\; (21 \mid 17^{k} + 4^{k}) \Rightarrow ((Prime\left((17^{k} + 4^{k}) / (21)\right)) \Rightarrow (Prime\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a228558` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a228558-price-seventeen-four-prime-exponent` (proved) by `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a228558`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a228558-price-seventeen-four-prime-exponent","declaration_gid":"D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a228558","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Price (2013). *OEIS A228558, Numbers k such that (17^k + 4^k)/21 is prime*. URL: <https://oeis.org/A228558>.

*Commentary.*

For every natural exponent k, if 21 divides 17^k+4^k and the exact quotient (17^k+4^k)/21 is prime, then k is prime. The explicit divisibility hypothesis prevents natural-number division from silently truncating. The general theorem applies because 4 is positive, 4<17, and 17 and 4 are coprime.

**Theorem 1.3 (Price's A231329 exponent conjecture).**

$$\forall k \in \mathrm{Nat},\; (23 \mid 19^{k} + 4^{k}) \Rightarrow ((Prime\left((19^{k} + 4^{k}) / (23)\right)) \Rightarrow (Prime\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a231329` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a231329-price-nineteen-four-prime-exponent` (proved) by `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a231329`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a231329-price-nineteen-four-prime-exponent","declaration_gid":"D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a231329","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Price (2013). *OEIS A228558, Numbers k such that (17^k + 4^k)/21 is prime*. URL: <https://oeis.org/A228558>.

*Commentary.*

For every natural exponent k, if 23 divides 19^k+4^k and the exact quotient (19^k+4^k)/23 is prime, then k is prime. The explicit divisibility hypothesis prevents natural-number division from silently truncating. The general theorem applies because 4 is positive, 4<19, and 19 and 4 are coprime.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.prime_quotient_exponent_is_prime`
- Truth anchor: `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a228558`
- Truth anchor: `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a231329`
