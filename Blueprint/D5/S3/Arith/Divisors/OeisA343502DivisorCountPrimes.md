# The OEIS A343502 Divisor-Count Prime Conjecture

## Abstract

Dequatre's OEIS A343502 conjecture: every member except 2 and 3 is composite.

**Definition 1.1 (The defining membership condition for A343502).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{InA343502}\left(k\right)) \Leftrightarrow ((1 \le k) \land ((\operatorname{Prime}\left(\operatorname{card}\left(\operatorname{divisors}\left(\operatorname{card}\left(\operatorname{divisors}\left(k\right)\right)\right)\right)\right)) \land (\operatorname{Prime}\left(\operatorname{card}\left(\operatorname{divisors}\left(k + 1\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.InA343502` (`✓ std3`).

*Citation.* C. H. R. Dequatre (2021). *OEIS A343502, Numbers k such that tau(tau(k)) and tau(k+1) are both prime*. URL: <https://oeis.org/A343502>.

*Commentary.*

The OEIS entry defines the sequence as numbers k such that tau(tau(k)) and tau(k+1) are both prime, where tau is the number of divisors function. The displayed expression expands tau literally as the cardinality of Nat.divisors and includes the positive-integer condition 1 ≤ k.

**Definition 1.2 (Dequatre's conjecture).**

$$\operatorname{claim}\left(\right) = \left(\forall k \in \mathrm{Nat},\; (\operatorname{InA343502}\left(k\right)) \Rightarrow ((k \ne 2) \Rightarrow ((k \ne 3) \Rightarrow ((1 < k) \land (\neg \operatorname{Prime}\left(k\right)))))\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.claim` (`✓ std3`).

*Citation.* C. H. R. Dequatre (2021). *OEIS A343502, Numbers k such that tau(tau(k)) and tau(k+1) are both prime*. URL: <https://oeis.org/A343502>.

*Commentary.*

The OEIS comment states verbatim: “Conjecture: all members except 2 and 3 are composite.” Here composite is encoded by 1 < k and the negation of Nat.Prime k, while membership retains the positive-index and two-prime conditions above.

**Theorem 1.3 (The conjecture holds).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{InA343502}\left(k\right)) \Rightarrow ((k \ne 2) \Rightarrow ((k \ne 3) \Rightarrow ((1 < k) \land (\neg \operatorname{Prime}\left(k\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a343502-divisor-count-primes-dequatre` (proved) by `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a343502-divisor-count-primes-dequatre","declaration_gid":"D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. H. R. Dequatre (2021). *OEIS A343502, Numbers k such that tau(tau(k)) and tau(k+1) are both prime*. URL: <https://oeis.org/A343502>.

*Commentary.*

Assume k is a member other than 2 or 3. If k were prime, it would be odd, so k + 1 would be even. The prime divisor count of k + 1 forces every prime factor of k + 1 to be 2; hence k + 1 is a power of 2. The exponent is prime, and the primality of the divisor count makes the exponent equal to 2, forcing k = 3, a contradiction.

The proof therefore establishes 1 < k and not Nat.Prime k for every remaining member. The separate OEIS question about whether A343502 has finitely many odd terms is not asserted here.

## References

- Truth anchor: `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.InA343502`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.claim`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.result`
- Dependency: [D5/S3/Arith/DivisorCountRadicalCoincidence](../DivisorCountRadicalCoincidence.md)
- Dependency: [D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample](../../Factorization/FactorDensityHighlyCompositeCounterexample.md)
