# Zelinsky and Zhang's Conjecture 22

## Abstract

The integer 6 refutes a published lower bound for a divisor-weighted logarithmic sum.

**Definition 1.1 (The divisor-weighted sum).**

$$\forall n \in \mathrm{Nat},\; \operatorname{v}\left(n\right) = \sum_{d \in Finset.filter\left(Nat.divisors\left(n\right), (\lambda d \mapsto 1 < d)\right)} (\frac{1}{(d : \mathrm{Real})} \cdot Real.log\left(\frac{(\operatorname{card}\left(Nat.divisors\left(n\right)\right) - 1 : \mathrm{Real})}{(d : \mathrm{Real})}\right))$$

*Formalization.* `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.v` (`✓ std3`).

*Citation.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

For every natural n, v(n) sums over exactly the divisors d of n with d greater than one. Each summand is 1/d times the natural logarithm of (card(divisors(n)) - 1)/d, with all quotients taken in the reals.

**Definition 1.2 (Conjecture 22).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (0 < n) \Rightarrow ((\neg n \in \{1, 12, 24, 30, 36, 48, 60, 72, 120, 180, 240, 360\}) \Rightarrow (\frac{1}{(Nat.minFac\left(n\right) : \mathrm{Real})^{2}} \le \operatorname{v}\left(n\right))))$$

*Formalization.* `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.claim` (`✓ std3`).

*Citation.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

For every positive natural n outside exactly the twelve displayed exclusions, the conjecture bounds v(n) below by the reciprocal square of Nat.minFac(n). No further condition on n is imposed.

**Theorem 1.3 (Conjecture 22 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-zhang-conjecture-22-refutation` (refuted) by `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-zhang-conjecture-22-refutation","declaration_gid":"D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

At n = 6 the retained divisors are 2, 3, and 6, while Nat.minFac(6) = 2. The sum reduces to one half times log(3/2) plus one sixth times log(1/2). The inequalities log(3/2) < 1/2 and log(1/2) < 0 make this value strictly less than 1/4, contradicting the asserted lower bound.

## References

- Truth anchor: `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.claim`
- Truth anchor: `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.result`
- Truth anchor: `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.v`
