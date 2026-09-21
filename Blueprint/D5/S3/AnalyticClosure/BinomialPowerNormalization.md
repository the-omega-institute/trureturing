# Complete Binomial Power Normalization

## Abstract

The complete sum of every positive integer power of binomial masses has its classical normalization.

**Theorem 1.1 (Exact Gaussian normalization for all positive natural powers).**

Lean statement: `D5/S3/AnalyticClosure/BinomialPowerNormalization.binomial_power_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialPowerNormalization.binomial_power_normalization` (`✓ std3`). ∎

*Citation.* Ulrich Abel, Wolfgang Gawronski, and Thorsten Neuschel (2013). *Binomial Polynomials*. DOI: [10.1007/s40315-013-0013-3](https://doi.org/10.1007/s40315-013-0013-3). URL: <https://doras.dcu.ie/31197/1/Binomialpolynomials.pdf>.

*Commentary.*

For each fixed 0<p<1 and positive natural l, the complete sum of binomialMass(p,n,i)^l over 0<=i<=n, divided by (2 pi n p(1-p))^((1-l)/2)/sqrt(l), tends to one. The exponent uses real subtraction, including l=1.

For l>=2 this is the classical weighted complete-sum estimate of Theorem 3.1 under r=l-1 and z=a^l, with p=a/(1+a). The case l=1 is exact by the binomial theorem. The local Gaussian source also gives the l=2,3 cases in equations (3.12)-(3.13): `D5/L/Analytic/ouimet2020precise`. These denominator estimates do not settle the maximum of the truncated ratio.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialPowerNormalization.binomial_power_normalization`
- Dependency: [D5/S3/AnalyticClosure/BinomialLocalGaussian](BinomialLocalGaussian.md)
