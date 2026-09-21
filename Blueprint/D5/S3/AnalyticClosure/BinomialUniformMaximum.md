# Uniform Binomial Upper Bound

## Abstract

A sharp Gaussian upper bound holds uniformly over all binomial indices.

**Theorem 1.1 (Uniform upper bound without a mode assumption).**

Lean statement: `D5/S3/AnalyticClosure/BinomialUniformMaximum.uniform_upper`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialUniformMaximum.uniform_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frédéric Ouimet (2020). *A precise local limit theorem for the multinomial distribution and some applications*. DOI: [10.1016/j.jspi.2021.03.006](https://doi.org/10.1016/j.jspi.2021.03.006). URL: <https://arxiv.org/abs/2001.08512v4>.

*Commentary.*

For every real parameter p strictly between zero and one and every positive epsilon, all sufficiently large n satisfy binomialMass(p,n,k) sqrt(2 pi n p (1-p)) <= 1+epsilon at every k from zero through n. The proof combines the existing relative local Gaussian approximation with its scaled tail estimate. These are classical local-limit ingredients; the exact uniform formulation is derived in this module. It assumes no formula for the maximizing index and does not itself assert the powered-ratio maximum asymptotic.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialUniformMaximum.uniform_upper`
- Dependency: [D5/S3/AnalyticClosure/BinomialLocalGaussian](BinomialLocalGaussian.md)
