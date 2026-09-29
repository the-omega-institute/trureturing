# Real-time Edgeworth expansion for two Poisson jumps

## Abstract

Independent Poisson jumps with irrational ratio satisfy a uniform first Edgeworth expansion, a fixed-width local limit, and uniform atom decay.

**Theorem 1.1 (Uniform Edgeworth expansion, local limits, and atom decay).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.result`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Take independent Poisson counts with means lambda times p and lambda times q. The weighted sum has mean lambda times (pa+qb) and variance lambda times (p a squared+q b squared). Standardize by that exact mean and variance. The correction coefficient uses p a cubed+q b cubed, the raw third jump moment.

For every positive error tolerance, all sufficiently large real lambda satisfy the first Edgeworth estimate uniformly over every real threshold. Choose the raw-frequency cutoff first and then let square-root time grow; finite signed smoothing and the moving-cutoff estimate give the limit.

For every fixed positive width h, the probability that the unstandardized weighted sum lies in (y,y+h], multiplied by square-root lambda, converges uniformly in y to h divided by the square root of V times the standard Gaussian density at the standardized left endpoint. Uniform continuity of the Gaussian density and its correction controls the difference of the two distribution functions.

The mass at every standardized score, multiplied by square-root lambda, tends uniformly to zero. The comparison distribution function is continuous, so its uniform error bounds the jump of the actual distribution function. All three conclusions use arbitrary fixed positive rates and arbitrary real jump sizes subject to the nonzero denominator and irrational-ratio hypotheses.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.result`
- Dependency: [D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthCutoff](CompoundPoissonEdgeworthCutoff.md)
