# Cumulative prime-tail phase error

## Abstract

Logarithmic error in the cumulative prime-tail mass

**Theorem 1.1 (Two-sided logarithmic order at the critical spectral gap).**

$$\forall rho \in \mathbb{C},\; \operatorname{NontrivialZero}\left(rho\right) \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(rho\right) \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le \operatorname{Re}\left(rho\right)\right) \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \left(\operatorname{Re}\left(z\right) < \operatorname{Re}\left(rho\right) \Rightarrow \operatorname{Re}\left(z\right) \le \frac{1}{2}\right)\right) \Rightarrow \left(\exists c \in \mathbb{R},\; 0 < c \land \left(\exists C \in \mathbb{R},\; 0 < C \land \exists B_{0}: \mathbb{R}, \forall B \in \mathbb{R},\; B_{0} \le B \Rightarrow \left(c \cdot \operatorname{log}\left(B\right) \le \operatorname{N}\left(2, B\right) - B^{\operatorname{Re}\left(rho\right) - \frac{1}{2}} \cdot I_{\infty}(Re, \operatorname{Re}\left(rho\right), \operatorname{phi}\left(\operatorname{log}\left(B\right)\right)) \land \operatorname{N}\left(2, B\right) - B^{\operatorname{Re}\left(rho\right) - \frac{1}{2}} \cdot I_{\infty}(Re, \operatorname{Re}\left(rho\right), \operatorname{phi}\left(\operatorname{log}\left(B\right)\right)) \le C \cdot \operatorname{log}\left(B\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthRate.prime_tail_cumulative_error_log_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let Qθ(x) be the integral of (θ(u)−u)/u² over u>x in Zhao's equation (14). Write N(a,B) for the integral of max(−Qθ(x),0)/√x from a to B. Let β=Re ρ for the stated zero and put p=β−1/2. The simultaneous phase orbit φ uses the actual zero occurrences with multiplicity. The integral I∞ uses the line at β and the weight exp(−ps) on past lags s>0.

In log time u, let q(u)=exp((1−β)u)Qθ(exp u) and let F(u) be the β-line profile at φ(u) and lag zero. After subtracting the β-line, the remaining root-scaled spectral sum is bounded in norm by the sum of the coefficient norms. The complete-tail correction is O(exp(−u)) before root scaling, and the root-scaled prime-power correction tends to 2. The signed residual exp(pu)(q(u)−F(u)) is bounded in absolute value and is eventually at most −1.

Choose W one unit above the critical width. The weighted negative-part integral is nonnegative on the compact phase closure. A zero there would give a zero cluster value for normalized arithmetic mass and force its lower limit to vanish. Continuity gives a positive minimum. Because the weight is at most one, the unweighted negative part of F has at least that much integral on every interval of length W.

The root-scaled difference of negative parts D(u) is eventually nonnegative and bounded. When F(u)≤0 it is at least 1. If F⁻≤M, this implies D≥F⁻/(M+1), so each full late interval of width W contributes uniformly positive mass. Summing adjacent intervals up to log B gives a linear lower bound up to a constant. Boundedness gives the linear upper bound.

The fixed-window substitution identifies the truncated discrepancy with the integral of D from log 2 to log B. The initial segment has fixed mass. After multiplication by B^p, the omitted phase tail beyond log B−log 2 is bounded by a constant as well. The inequalities follow by absorbing both constants at a sufficiently large real endpoint.

**Theorem 1.2 (Uniform error with a lower spectral ceiling).**

$$\forall beta \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; \frac{1}{2} \le gamma \Rightarrow \left(gamma < beta \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le beta\right) \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \left(\operatorname{Re}\left(z\right) < beta \Rightarrow \operatorname{Re}\left(z\right) \le gamma\right)\right) \Rightarrow \left(\exists K \in \mathbb{R},\; 0 < K \land \left(\forall B \in \mathbb{R},\; \forall a \in \mathbb{R},\; \left(2 \le a \land a \le B\right) \Rightarrow \left(\left(gamma = \frac{1}{2} \Rightarrow \left|\operatorname{E}\left(a, B\right)\right| \le K \cdot \left(\frac{a}{B}^{beta - \frac{1}{2}} + B^{-\left(beta - \frac{1}{2}\right)} \cdot \operatorname{log}\left(\frac{B}{a}\right)\right)\right) \land \left(\frac{1}{2} < gamma \Rightarrow \left|\operatorname{E}\left(a, B\right)\right| \le K \cdot \left(\frac{a}{B}^{beta - \frac{1}{2}} + B^{gamma - beta}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthRate.prime_tail_window_error_of_lower_spectral_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

For each pair β, γ satisfying the displayed assumptions, one K works for every real B and every left endpoint in [2,B]. The β-line may be empty. Here E(a,B)=N(a,B)/B^p−I∞(Re,β,φ(log B)).

Subtract the exact β-line from the root-scaled zero series. Each remaining term has norm at most its coefficient norm times exp((γ−1/2)u). The same majorant absorbs the bounded corrections on the late tail and extends to the fixed initial interval by continuity. The negative part is 1-Lipschitz, so the majorant also bounds the absolute log density error.

The fixed-window substitution integrates that bound from log a to log B. When γ>1/2, this gives a constant times B^(γ−1/2), and dividing by B^p gives B^(γ−β). At γ=1/2 the integrated majorant is proportional to log(B/a). The omitted phase tail contributes the term (a/B)^p in both cases.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthRate.prime_tail_cumulative_error_log_order`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthRate.prime_tail_window_error_of_lower_spectral_bound`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalResidual](PrimeCriticalResidual.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster](PrimeGrowingWidthCluster.md)
