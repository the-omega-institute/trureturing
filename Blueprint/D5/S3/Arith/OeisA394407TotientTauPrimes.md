# Huber's Prime Conjecture for OEIS A394407

## Abstract

Every prime other than three first attains its totient-to-divisor-count ratio.

The variables k, m and p are natural numbers. Nat.totient is Euler's totient, Nat.divisors is the finite set of positive divisors, and Finset.card counts those divisors. Both operands of division are explicitly cast to Q, so division is rational division. The sequence concerns positive integers.

**Definition 1.1 (The totient-to-divisor-count ratio).**

$$\forall m \in \mathbb{N},\; \operatorname{ratio}\left(m\right) = \frac{(\operatorname{Nat}.\operatorname{totient}\left(m\right): \mathbb{Q})}{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Nat}.\operatorname{divisors}\left(m\right)\right): \mathbb{Q})}$$

*Formalization.* `D5/S3/Arith/OeisA394407TotientTauPrimes.ratio` (`✓ std3`).

*Citation.* Felix Huber (2026). *OEIS A394407: first occurrences of the totient-to-divisor-count ratio*. URL: <https://oeis.org/A394407>.

*Commentary.*

OEIS A394407, unpaginated Name line: "Positive integers k such that there is no m < k with phi(m)/tau(m) = phi(k)/tau(k)." The expression phi(m)/tau(m) is the quotient of Nat.totient m and Finset.card (Nat.divisors m), each cast to Q. The total function also has value zero at m = 0; the sequence uses only positive inputs.

**Definition 1.2 (First occurrence of a ratio).**

$$\forall k \in \mathbb{N},\; \operatorname{IsTerm}\left(k\right) = ((0 < k) \land (\forall m \in \mathbb{N},\; (0 < m) \Rightarrow ((m < k) \Rightarrow (\operatorname{ratio}\left(m\right) \ne \operatorname{ratio}\left(k\right)))))$$

*Formalization.* `D5/S3/Arith/OeisA394407TotientTauPrimes.IsTerm` (`✓ std3`).

*Citation.* Felix Huber (2026). *OEIS A394407: first occurrences of the totient-to-divisor-count ratio*. URL: <https://oeis.org/A394407>.

*Commentary.*

OEIS A394407, unpaginated Name line: "Positive integers k such that there is no m < k with phi(m)/tau(m) = phi(k)/tau(k)." IsTerm k requires k > 0 and compares its ratio with every positive m < k. The domain of m follows the positive-integer sequence and its examples.

**Definition 1.3 (Huber's conjecture).**

$$\operatorname{claim} = (\forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((p \ne 3) \Rightarrow (\operatorname{IsTerm}\left(p\right))))$$

*Formalization.* `D5/S3/Arith/OeisA394407TotientTauPrimes.claim` (`✓ std3`).

*Citation.* Felix Huber (2026). *OEIS A394407: first occurrences of the totient-to-divisor-count ratio*. URL: <https://oeis.org/A394407>.

*Commentary.*

OEIS A394407, unpaginated Comment line: "Conjecture: All primes p != 3 are in the sequence; equivalently, for every prime p != 3 there is no m < p with phi(m)/tau(m) = phi(p)/tau(p) = (p - 1)/2; equivalently, the sequence is a supersequence of A045344." Nat.Prime p and p != 3 are the two hypotheses; IsTerm p expresses membership by the positive-integer first-occurrence condition.

**Theorem 1.4 (Every prime other than three is a term).**

$$\forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((p \ne 3) \Rightarrow (\operatorname{IsTerm}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OeisA394407TotientTauPrimes.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a394407-totient-tau-primes-huber` (proved) by `D5/S3/Arith/OeisA394407TotientTauPrimes.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a394407-totient-tau-primes-huber","declaration_gid":"D5/S3/Arith/OeisA394407TotientTauPrimes.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Felix Huber (2026). *OEIS A394407: first occurrences of the totient-to-divisor-count ratio*. URL: <https://oeis.org/A394407>.

*Commentary.*

For a prime p the divisor set is {1, p}, so its ratio is (p - 1)/2. If m = 1, equality with that ratio forces p = 3. If 2 <= m < p, Nat.totient m < m and there are at least two positive divisors, giving ratio m <= Nat.totient m / 2 < (p - 1)/2. These cases exclude every smaller positive m.

## References

- Truth anchor: `D5/S3/Arith/OeisA394407TotientTauPrimes.IsTerm`
- Truth anchor: `D5/S3/Arith/OeisA394407TotientTauPrimes.claim`
- Truth anchor: `D5/S3/Arith/OeisA394407TotientTauPrimes.ratio`
- Truth anchor: `D5/S3/Arith/OeisA394407TotientTauPrimes.result`
