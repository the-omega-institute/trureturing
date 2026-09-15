# The OEIS A089610 Eventual Strict-Increase Conjecture

## Abstract

Odd-prime counting rules out eventual strict increase for OEIS A089610.

**Definition 1.1 (The square-interval prime count).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(Nat.Prime, \operatorname{Ioc}\left(n \cdot n, n \cdot n + n\right)\right)\right)$$

*Formalization.* `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.a` (`✓ std3`).

*Citation.* Cino Hilliard (2003). *OEIS A089610, Number of primes between n^2 and (n+1/2)^2*. URL: <https://oeis.org/A089610>.

*Commentary.*

The value a(n) counts the primes in the half-open interval (n^2, n^2+n]. Since (n+1/2)^2 = n^2+n+1/4, this interval contains the same integer primes as the printed OEIS interval.

**Definition 1.2 (The eventual strict-increase conjecture).**

$$(claim) \Leftrightarrow (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (\operatorname{a}\left(n\right) < \operatorname{a}\left(n + 1\right)))$$

*Formalization.* `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.claim` (`✓ std3`).

*Citation.* Cino Hilliard (2003). *OEIS A089610, Number of primes between n^2 and (n+1/2)^2*. URL: <https://oeis.org/A089610>.

*Commentary.*

The claim asks for a natural threshold N after which every successive value of a is strictly larger.

**Theorem 1.3 (Eventual strict increase is impossible).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a089610-square-interval-prime-count-eventual-increase-refutation` (refuted) by `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a089610-square-interval-prime-count-eventual-increase-refutation","declaration_gid":"D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Cino Hilliard (2003). *OEIS A089610, Number of primes between n^2 and (n+1/2)^2*. URL: <https://oeis.org/A089610>.

*Commentary.*

At every even index, the odd primes in the defining interval inject into k positions, giving a(2k) <= k. Strict increase through a window from M to 2M+2 would instead force the final value above this bound. The first conjecture a(n) > 1 after n = 17 and Oppermann's positivity conjecture are untouched.

## References

- Truth anchor: `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.a`
- Truth anchor: `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.claim`
- Truth anchor: `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.result`
