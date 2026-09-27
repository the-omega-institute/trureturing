# Mathar's recurrence for A108958

## Abstract

The number a(n) of unordered pairs of distinct binary words of length n with the same number of 1's (the zero-quantum transitions of n spins 1/2) satisfies n(n - 2)a(n) + 2(-3n^2 + 7n - 3)a(n - 1) + 4(n - 1)(2n - 3)a(n - 2) = 0 for every n at least 2, as conjectured by R. J. Mathar for OEIS A108958.

**Definition 1.1 (Pairs of words with equal weight).**

$$\operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} \operatorname{choose}\left(\operatorname{choose}\left(n, k\right), 2\right)$$

*Formalization.* `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.a` (`✓ std3`).

*Citation.* R. J. Mathar (2012). *OEIS A108958, number of unordered pairs of distinct length-n binary words having the same number of 1's: recurrence conjecture*. URL: <https://oeis.org/A108958>.

*Commentary.*

The number of unordered pairs of distinct binary words of length n with the same number of 1's: for each k, the pairs among the choose(n, k) words with k ones.

**Definition 1.2 (Mathar's conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 2 \le n \Rightarrow (n \cdot (n - 2) \cdot \operatorname{a}\left(n\right) + 2 \cdot (-3 \cdot n^{2} + 7 \cdot n - 3) \cdot \operatorname{a}\left(n - 1\right) + 4 \cdot (n - 1) \cdot (2 \cdot n - 3) \cdot \operatorname{a}\left(n - 2\right) = 0))$$

*Formalization.* `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar (2012). *OEIS A108958, number of unordered pairs of distinct length-n binary words having the same number of 1's: recurrence conjecture*. URL: <https://oeis.org/A108958>.

*Commentary.*

For every n at least 2 the three-term recurrence with polynomial coefficients holds.

**Theorem 1.3 (Proof of the recurrence).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2012-a108958-recurrence` (proved) by `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2012-a108958-recurrence","declaration_gid":"D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar (2012). *OEIS A108958, number of unordered pairs of distinct length-n binary words having the same number of 1's: recurrence conjecture*. URL: <https://oeis.org/A108958>.

*Commentary.*

Since C(c, 2) = c(c - 1)/2, twice a(n) is the sum of the squares of the binomial coefficients C(n, k) minus their sum, that is C(2n, n) - 2^n. The central binomial coefficients satisfy (k + 1)C(2k + 2, k + 1) = 2(2k + 1)C(2k, k); applying this twice turns the recurrence for C(2n, n) into 2[(n - 2)(2n - 1) - (3n^2 - 7n + 3) + (n - 1)^2] C(2n - 2, n - 1) = 0, and 2^n satisfies it because 4n(n - 2) - 4(3n^2 - 7n + 3) + 4(n - 1)(2n - 3) = 0. The recurrence is linear, so a(n) satisfies it.

## References

- Truth anchor: `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.a`
- Truth anchor: `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.result`
