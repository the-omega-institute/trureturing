# The OEIS A079063 Square-Root Lower-Bound Conjecture

## Abstract

Prime counting refutes the eventual square-root lower bound proposed for A079063.

**Definition 1.1 (The least square-root prime-gap index).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{sInf}\left(\{k \in \mathrm{Nat} \mid ((0 < k) \land (1 < \operatorname{sqrt}\left(\operatorname{nth}\left(Prime, n + k - 1\right)\right) - \operatorname{sqrt}\left(\operatorname{nth}\left(Prime, n - 1\right)\right)))\}\right)$$

*Formalization.* `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.a` (`✓ std3`).

*Citation.* Benoit Cloitre (2003). *OEIS A079063, Least k such that sqrt(prime(n+k))-sqrt(prime(n))>1*. URL: <https://oeis.org/A079063>.

*Commentary.*

Here prime(n) is the n-th prime, represented as Nat.nth Nat.Prime (n-1). For n at least one the witness set is nonempty, so sInf is its least member. If the set is empty, the natural-number convention sInf empty equals zero.

**Definition 1.2 (The eventual positive square-root lower bound).**

$$(claim) \Leftrightarrow (\exists c \in \mathrm{Real},\; (0 < c) \land (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (c \cdot \operatorname{sqrt}\left((n : \mathrm{Real})\right) < (\operatorname{a}\left(n\right) : \mathrm{Real}))))$$

*Formalization.* `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.claim` (`✓ std3`).

*Citation.* Benoit Cloitre (2003). *OEIS A079063, Least k such that sqrt(prime(n+k))-sqrt(prime(n))>1*. URL: <https://oeis.org/A079063>.

*Commentary.*

This is the weakest quantified reading of the conjecture: some positive real constant bounds a(n) strictly below by c times the square root of n for every sufficiently large natural n.

**Theorem 1.3 (The eventual lower bound is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a079063-sqrt-prime-gap-lower-bound-refutation` (refuted) by `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a079063-sqrt-prime-gap-lower-bound-refutation","declaration_gid":"D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benoit Cloitre (2003). *OEIS A079063, Least k such that sqrt(prime(n+k))-sqrt(prime(n))>1*. URL: <https://oeis.org/A079063>.

*Commentary.*

A local one-unit square-root increment bound is iterated over blocks of length 3r^2 to obtain a linear upper bound for square roots of quadratic-index primes. The resulting quadratic lower bound on prime counting contradicts the Chebyshev upper bound.

## References

- Truth anchor: `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.a`
- Truth anchor: `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.claim`
- Truth anchor: `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.result`
