# Binomial entropy at a moving interior proportion

## Abstract

Binomial entropy at a moving interior proportion.

**Theorem 1.1 (Moving binomial exponent).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy.log_choose_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy.log_choose_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any filter, any real scale y tending to positive infinity, and natural functions n and k with n/y tending to d>0 and k/y tending to r with 0<r<d, log(choose(n,k))/y tends to d*binEntropy(r/d). The proof uses the pinned Stirling sequence limit at n, k and n-k, the exact factorial quotient, and logarithmic errors divided by the growing scale. It does not require a Gaussian window or a rate of convergence of k/n.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy.log_choose_scaled`
