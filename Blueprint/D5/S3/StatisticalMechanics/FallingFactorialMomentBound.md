# A bound on n^2 times a falling factorial

## Abstract

For every integer k >= 1 and every integer 0 <= n <= k, n^2/k (1/k)^n k!/(k - n)! <= 1, that is, n^2 k(k - 1)...(k - n + 1) <= k^(n + 1). This is the conjecture stated after eq. (003.21) by T. A. Malik and R. Lopez-Mobilia (arXiv:2004.07168), who checked it numerically; they use it for the corollary h(k) in (1/k, k), which is not formalized here.

**Definition 1.1 (The conjecture).**

$$claim \Leftrightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow \left(\forall n \in \mathbb{N},\; (n \le k) \Rightarrow \frac{n^{2}}{k} \cdot (\frac{1}{k})^{n} \cdot (\frac{k!}{(k - n)!}) \le 1\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/FallingFactorialMomentBound.claim` (`✓ std3`).

*Citation.* Taha A. Malik; Rafael Lopez-Mobilia (2020). *A new phenomenological definition of entropy and application to black holes*. URL: <https://arxiv.org/abs/2004.07168v1>.

*Commentary.*

The conjecture after eq. (003.21) of the paper, written with k for k'. Here k - n is subtraction of natural numbers, exact since n <= k, and the factorials are read in the real numbers.

**Theorem 1.2 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/FallingFactorialMomentBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/malik-2020-falling-factorial-moment-bound` (proved) by `D5/S3/StatisticalMechanics/FallingFactorialMomentBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"malik-2020-falling-factorial-moment-bound","declaration_gid":"D5/S3/StatisticalMechanics/FallingFactorialMomentBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Taha A. Malik; Rafael Lopez-Mobilia (2020). *A new phenomenological definition of entropy and application to black holes*. URL: <https://arxiv.org/abs/2004.07168v1>.

*Commentary.*

Since k!/(k - n)! = k(k - 1)...(k - n + 1), the claim is n^2 k(k - 1)...(k - n + 1) <= k^(n + 1). For n <= 3 this is direct: n = 2 reads 4(k - 1) <= k^2, and n = 3 reads 9 k(k - 1)(k - 2) <= k^4, which follows from k^4 - 9 k(k - 1)(k - 2) = k((k - 3)^3 + 9). For n >= 4, k(k - 1)...(k - n + 1) = k^n times the product of 1 - i/k over i < n, and 1 - x <= e^(-x) bounds this product by e^(-u) with u = n(n - 1)/(2k). Since u e^(-u) <= e^(-1) < 3/8, (n - 1) n^2 e^(-u) = 2 n k u e^(-u) <= (3/4) n k <= (n - 1) k, so n^2 e^(-u) <= k and the claim follows.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/FallingFactorialMomentBound.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/FallingFactorialMomentBound.result`
