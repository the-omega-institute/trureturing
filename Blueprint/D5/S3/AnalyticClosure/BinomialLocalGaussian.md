# Binomial Gaussian Ingredients

## Abstract

Binomial local Gaussian approximation, negligible powered tails, and lattice Gaussian sums.

**Definition 1.1 (Binomial probability mass).**

Lean statement: `D5/S3/AnalyticClosure/BinomialLocalGaussian.binomialMass`

*Formalization.* `D5/S3/AnalyticClosure/BinomialLocalGaussian.binomialMass` (`✓ std3`).

*Citation.* Frédéric Ouimet (2020). *A precise local limit theorem for the multinomial distribution and some applications*. DOI: [10.1016/j.jspi.2021.03.006](https://doi.org/10.1016/j.jspi.2021.03.006). URL: <https://arxiv.org/abs/2001.08512v4>.

*Commentary.*

binomialMass(p,n,i) = choose(n,i) p^i (1-p)^(n-i). The probability interpretation used here requires 0<p<1 and 0<=i<=n.

**Definition 1.2 (Binary relative entropy expression).**

Lean statement: `D5/S3/AnalyticClosure/BinomialLocalGaussian.binaryKL`

*Formalization.* `D5/S3/AnalyticClosure/BinomialLocalGaussian.binaryKL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

binaryKL(x,p) = x log(x/p) + (1-x) log((1-x)/(1-p)). It is the entropy expression used in the Stirling expansion; this definition carries no claim of mathematical novelty.

**Theorem 1.3 (Uniform relative approximation on a growing window).**

Lean statement: `D5/S3/AnalyticClosure/BinomialLocalGaussian.local_gaussian_window`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialLocalGaussian.local_gaussian_window` (`✓ std3`). ∎

*Citation.* Frédéric Ouimet (2020). *A precise local limit theorem for the multinomial distribution and some applications*. DOI: [10.1016/j.jspi.2021.03.006](https://doi.org/10.1016/j.jspi.2021.03.006). URL: <https://arxiv.org/abs/2001.08512v4>.

*Commentary.*

For each fixed 0<p<1 and every epsilon>0, all sufficiently large natural n and every natural k with |k-np|<=n^(7/12) satisfy |binomialMass(p,n,k) sqrt(2 pi n p(1-p)) exp((k-np)^2/(2 n p(1-p))) - 1| < epsilon. This is a binomial specialization of the classical local-limit estimate in Theorem 2.1 and its proof.

**Theorem 1.4 (Powered tails beat every fixed polynomial scale).**

Lean statement: `D5/S3/AnalyticClosure/BinomialLocalGaussian.binomial_power_tail`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialLocalGaussian.binomial_power_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frédéric Ouimet (2020). *A precise local limit theorem for the multinomial distribution and some applications*. DOI: [10.1016/j.jspi.2021.03.006](https://doi.org/10.1016/j.jspi.2021.03.006). URL: <https://arxiv.org/abs/2001.08512v4>.

*Commentary.*

For fixed 0<p<1, every positive natural l and every real s, n^s times the sum of binomialMass(p,n,i)^l over 0<=i<=n with |i-np|>n^(7/12) tends to zero. The proof uses the binomial theorem and the frozen binary Pinsker inequality, including both boundary indices. This is a classical tail ingredient in the repository's precise finite-sum formulation.

**Theorem 1.5 (Gaussian lattice sum with a moving real center).**

Lean statement: `D5/S3/AnalyticClosure/BinomialLocalGaussian.gaussian_window_sum_limit`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialLocalGaussian.gaussian_window_sum_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed 0<p<1 and c>0, the sum of exp(-c ((i-np)/sqrt(n))^2) over 0<=i<=n with |i-np|<=n^(7/12), divided by sqrt(n), tends to sqrt(pi/c). The center np need not be integral. Sum-integral comparison and Gaussian tails supply this auxiliary limit; it is not a powered-ratio maximum result.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialLocalGaussian.binaryKL`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialLocalGaussian.binomialMass`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialLocalGaussian.binomial_power_tail`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialLocalGaussian.gaussian_window_sum_limit`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialLocalGaussian.local_gaussian_window`
- Dependency: [D5/S3/TotalVariation/Pinsker](../TotalVariation/Pinsker.md)
