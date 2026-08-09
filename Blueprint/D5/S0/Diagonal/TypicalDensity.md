# Typical Minimum-Distance Density

## Abstract

The minimum diagonal-distance density concentrates between any fixed lower and upper densities straddling the nonzero-choice density.

**Theorem 1.1 (Binomial upper-tail KL bound).**

$$\operatorname{Pr}\left(\operatorname{Bin}\left(r, p\right), \ge, q \cdot r\right)\le\operatorname{exp}\left(0 - r \cdot \operatorname{bernoulliKL}\left(q, p\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/TypicalDensity.binomial_upper_tail_kl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p below q below one, the positive exponential tilt in the standard moment-generating-function Chernoff inequality gives the upper-tail rate KL(q||p). The Bernoulli KL definition is reused from MarginBound.

**Theorem 1.2 (The minimum upper tail reduces to one row).**

$$\operatorname{upperFailureProbability}\left(f, alpha\right) \le \operatorname{rowUpperProbability}\left(f, alpha\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/TypicalDensity.upper_failure_probability_le_row_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event that the minimum exceeds a threshold forces every row, hence any fixed row, to exceed it. The exact distance-profile factorization makes the minimum probability a power of the single-row factor; since that factor lies in the unit interval, the power is no larger.

**Theorem 1.3 (Two-sided typical density).**

$$\lim_{A\to\infty}\operatorname{typicalDensityFailureProbability}\left(f, alpha_{lo}, alpha_{hi}\right)=0.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/TypicalDensity.typical_density_failure_probability_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix zero below alpha_lo below p below alpha_hi below one, where p is the nonzero-choice density (n-1)/n. The lower failure probability vanishes by MarginVanishing. For the upper failure, every row distance is at most one plus a Bin(A-1,p) count; the preceding single-row reduction and upper-tail KL bound make this probability vanish. A finite union bound combines the two sides. Thus the minimum distance lies in [alpha_lo A, alpha_hi A] outside a set of probability tending to zero.

## References

- Truth anchor: `D5/S0/Diagonal/TypicalDensity.binomial_upper_tail_kl`
- Truth anchor: `D5/S0/Diagonal/TypicalDensity.typical_density_failure_probability_tendsto_zero`
- Truth anchor: `D5/S0/Diagonal/TypicalDensity.upper_failure_probability_le_row_probability`
- Dependency: [D5/S0/Diagonal/MarginVanishing](MarginVanishing.md)
