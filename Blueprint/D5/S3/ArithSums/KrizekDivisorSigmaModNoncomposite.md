# Krizek's A300657 noncomposite characterization

## Abstract

Krizek's divisor sum of sigma residues equals the final residue exactly at one and the primes.

All variables and values are natural numbers. The notation sigma(1,d) denotes the sum of the positive divisors of d, and b mod d denotes the natural-number remainder of b upon division by d.

**Definition 1.1 (The divisor sigma-residue sum).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a300657}\left(n\right) = \sum_{d \in \operatorname{divisors}\left(n\right)} \operatorname{sigma}\left(1, d\right) \bmod d$$

*Formalization.* `D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.a300657` (`✓ std3`).

*Citation.* Jaroslav Krizek (2018). *OEIS A300657, sum of divisor-sum residues*. URL: <https://oeis.org/A300657>.

*Commentary.*

For each n, the sum ranges over the positive divisors d of n and adds the remainder of sigma(1,d) modulo d. At zero the divisor set is empty; the characterization below starts at one.

**Theorem 1.2 (The noncomposite characterization).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((\operatorname{a300657}\left(n\right) = \operatorname{sigma}\left(1, n\right) \bmod n) \Leftrightarrow ((n = 1) \lor (\operatorname{Prime}\left(n\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a300657-krizek-divisor-sigma-mod-noncomposite` (proved) by `D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a300657-krizek-divisor-sigma-mod-noncomposite","declaration_gid":"D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek (2018). *OEIS A300657, sum of divisor-sum residues*. URL: <https://oeis.org/A300657>.

*Commentary.*

The entry states: "a(n) >= A054024(n). Conjecture: a(n) = A054024(n) only for the noncomposite numbers A008578." For every n at least one, the divisor residue sum equals the final sigma residue exactly when n is one or prime. For a composite n, its least prime factor is a proper divisor and contributes one modulo itself, so the remaining nonnegative divisor terms cannot sum to zero. At one and at a prime, the divisor set evaluates directly.

## References

- Truth anchor: `D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.a300657`
- Truth anchor: `D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.result`
