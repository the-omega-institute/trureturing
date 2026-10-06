# Scalar Gaussian even moments

## Abstract

The central even moments of a real Gaussian law are exact at every nonnegative variance.

**Theorem 1.1 (Exact moments including zero variance).**

$$\forall mu \in Real, sigma \in NNReal, n \in Nat,\; \operatorname{centralMoment}\left(id, 2 \cdot n, \operatorname{gaussianReal}\left(mu, sigma^{2}\right)\right) = sigma^{2 \cdot n} \cdot Nat.doubleFactorial\left({2 \cdot n-1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianEvenMoment.centralMoment_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For a real mean mu, nonnegative standard deviation sigma and natural n, the central moment of order 2n of N(mu,sigma^2) equals sigma^(2n) times (2n-1) double factorial. At n=0 the natural subtraction is truncated and the double factorial is one. The formula includes sigma=0.

Translation removes the mean. The centered Gaussian density is even, so the integral reduces to the positive half-line. The substitution x=sigma sqrt(2u) gives a Gamma integral at n+1/2, whose half-integer value supplies the double factorial. The second and fourth moments are sigma^2 and 3 sigma^4.

Its standard-normal specialization supplies the even moments used in the countable centered Gaussian quadratic-series theorem.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianEvenMoment.centralMoment_two_mul`
