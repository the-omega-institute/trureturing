# The OEIS A049591 Divisor-Count Prime-Gap Characterization

## Abstract

The value 529 refutes Cloitre's divisor-count prime-gap characterization.

**Definition 1.1 (Membership in A049591).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{Term}\left(n\right)) \Leftrightarrow ((\operatorname{Odd}\left(n\right)) \land \left((\operatorname{Prime}\left(n\right)) \land (\neg \operatorname{Prime}\left(n + 2\right))\right))$$

*Formalization.* `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.Term` (`✓ std3`).

*Citation.* Labos Elemer; Benoit Cloitre (2002). *OEIS A049591, Odd primes p such that p+2 is composite*. URL: <https://oeis.org/A049591>.

*Commentary.*

A natural n is a term when it is odd and prime while n+2 is not prime.

**Definition 1.2 (The prime-free interval condition).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{NoPrimeInGap}\left(n\right)) \Leftrightarrow (\forall p \in \mathrm{Nat},\; (\operatorname{Prime}\left(p\right)) \Rightarrow (\neg ((n < p) \land (p < n + \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right)^{2}))))$$

*Formalization.* `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.NoPrimeInGap` (`✓ std3`).

*Citation.* Labos Elemer; Benoit Cloitre (2002). *OEIS A049591, Odd primes p such that p+2 is composite*. URL: <https://oeis.org/A049591>.

*Commentary.*

NoPrimeInGap(n) means that no prime lies strictly between n and n plus the square of the number of divisors of n.

**Definition 1.3 (Cloitre's characterization).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (1 < n) \Rightarrow ((\operatorname{Term}\left(n\right)) \Leftrightarrow (\operatorname{NoPrimeInGap}\left(n\right))))$$

*Formalization.* `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.claim` (`✓ std3`).

*Citation.* Labos Elemer; Benoit Cloitre (2002). *OEIS A049591, Odd primes p such that p+2 is composite*. URL: <https://oeis.org/A049591>.

*Commentary.*

The characterization asserts that every natural n greater than one is a sequence term exactly when it satisfies the prime-free interval condition.

**Theorem 1.4 (The characterization fails at 529).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a049591-prime-gap-divisor-characterization-refutation` (refuted) by `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a049591-prime-gap-divisor-characterization-refutation","declaration_gid":"D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Labos Elemer; Benoit Cloitre (2002). *OEIS A049591, Odd primes p such that p+2 is composite*. URL: <https://oeis.org/A049591>.

*Commentary.*

The value 529 has exactly three divisors, and every integer strictly between 529 and 538 is composite, so NoPrimeInGap(529) holds. But 529 is not prime, so Term(529) fails. This refutes only Cloitre's gap characterization; the sequence definition and the entry's other comments are untouched.

## References

- Truth anchor: `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.NoPrimeInGap`
- Truth anchor: `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.Term`
- Truth anchor: `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.claim`
- Truth anchor: `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.result`
