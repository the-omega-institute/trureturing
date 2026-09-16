# Kurkov's Reversed q-Bell Row Polynomials

## Abstract

Kurkov's triangular recurrence produces the reversed q-Bell row polynomials.

All indices are natural numbers, including zero, and all polynomials lie in Z[X]. The expression binom(n,k) is the natural binomial coefficient cast to an integer constant polynomial. A sum with upper index k-1 ranges over j=0,...,k-1 and is empty when k=0. The reversal operator reflects coefficients about the natural degree.

**Definition 1.1 (The q-Bell row polynomials).**

$$\begin{aligned}\operatorname{qBell}\left(0\right) = 1\\\forall n \in \mathbb{N}, \operatorname{qBell}\left((n + 1)\right) = \sum_{k = 0}^{n} (\operatorname{binom}\left(n, k\right) \cdot \operatorname{qBell}\left(k\right) \cdot X^{k})\end{aligned}$$

*Formalization.* `D5/S1/Words/KurkovReversedQBellRowPolynomial.qBell` (`✓ std3`).

*Citation.* Paul D. Hanna; Carl G. Wagner; Jianping Pan; Tianyi Yu; Mikhail Kurkov (2025). *OEIS A126347 q-Bell coefficient triangle and Kurkov's reversed-row conjecture*. URL: <https://oeis.org/A126347>.

*Commentary.*

The initial row is one. Wagner's recurrence forms row n+1 from all rows through n, weighted by binom(n,k) X^k. These are the row polynomials whose coefficients form OEIS A126347.

**Definition 1.2 (Kurkov's triangular recurrence).**

$$\begin{aligned}\operatorname{R}\left(0, 0\right) = 1\\\forall k \in \mathbb{N}, \operatorname{R}\left(0, (k + 1)\right) = 0\\\forall n, k \in \mathbb{N}, \operatorname{R}\left((n + 1), k\right) = \operatorname{R}\left(n, n\right) + X^{(n + 1)} \cdot (\sum_{j = 0}^{k - 1} (\operatorname{R}\left(n, j\right)))\end{aligned}$$

*Formalization.* `D5/S1/Words/KurkovReversedQBellRowPolynomial.kurkovR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna; Carl G. Wagner; Jianping Pan; Tianyi Yu; Mikhail Kurkov (2025). *OEIS A126347 q-Bell coefficient triangle and Kurkov's reversed-row conjecture*. URL: <https://oeis.org/A126347>.

*Commentary.*

Row zero is one at column zero and zero at later columns. Every later entry adds the preceding diagonal to X^(n+1) times the prefix of row n. On the diagonal of row n+1 that prefix only reads columns j<=n, so the row-zero totalization cannot affect the theorem.

**Theorem 1.3 (Kurkov's reversed-row identity).**

$$\forall n \in \mathbb{N}, \operatorname{R}\left(n, n\right) = \operatorname{reverse}\left(\operatorname{qBell}\left((n + 1)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/KurkovReversedQBellRowPolynomial.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna; Carl G. Wagner; Jianping Pan; Tianyi Yu; Mikhail Kurkov (2025). *OEIS A126347 q-Bell coefficient triangle and Kurkov's reversed-row conjecture*. URL: <https://oeis.org/A126347>.

*Commentary.*

For every n, the diagonal entry R(n,n) is the coefficient reversal of qBell(n+1). The q-Bell polynomial is monic of degree binom(n+1,2), so natural-degree reversal agrees with reversal of the fixed-length OEIS row. A Pascal expansion of the R-prefix sums supplies the binomial convolution used by Wagner's recurrence.

## References

- Truth anchor: `D5/S1/Words/KurkovReversedQBellRowPolynomial.kurkovR`
- Truth anchor: `D5/S1/Words/KurkovReversedQBellRowPolynomial.qBell`
- Truth anchor: `D5/S1/Words/KurkovReversedQBellRowPolynomial.result`
