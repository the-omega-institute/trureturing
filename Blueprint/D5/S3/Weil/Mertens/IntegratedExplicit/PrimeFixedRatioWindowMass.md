# A lower bound from each off-line zero

## Abstract

Prime-tail negative mass on fixed-ratio windows

**Theorem 1.1 (The exponent of a supplied off-line zero).**

$$\forall rho \in \mathbb{C},\; \operatorname{NontrivialZero}\left(rho\right) \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(rho\right) \Rightarrow \left(\exists kappa \in \mathbb{R},\; \exists c \in \mathbb{R},\; \exists S \in \mathbb{R},\; 1 < kappa \land \left(0 < c \land \left(\forall B \in \mathbb{R},\; S \le B \Rightarrow \left(\forall A \in \mathbb{R},\; 2 \le A \Rightarrow \left(kappa \cdot A \le B \Rightarrow c \cdot B^{\operatorname{Re}\left(rho\right) - \frac{1}{2}} \le \operatorname{N}\left(A, B\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass.prime_tail_fixed_ratio_mass_of_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let Q be the tail obtained by integrating (ψ(t)−t)/t² above x, and let Qθ be the analogous prime-only tail with θ in place of ψ. Zhao's equation (14) uses this prime-only tail. Define N(A,B) as the integral of max(−Qθ(x),0)/√x from A to B.

For a nontrivial zero with real part β greater than one half, use the positive-ordinate member of its conjugate pair. A compact probability filter retains the pair and suppresses the other zeros to the right of a cutoff strictly between one half and β. The negative filtered tail has a leading cosine at scale exp((β−1)t). The ratio of the error bound to that scale is eventually at most one quarter of the cosine amplitude.

Every two-period log window contains a subinterval of fixed positive length on which the cosine is at least one half. Fubini exchanges the interval integral and the probability average. Every translate of this subinterval lies in the log window enlarged by the filter support. Its signed integral is bounded by the integral of the positive part of the unaveraged negative tail over the enlarged window.

On the enlarged window [T,T+W], the substitution x=exp(t) turns the weight dx/√x into exp(t/2) dt. The signed prime-power comparison gives Qθ≤Q, so the resulting prime-only mass is at least a positive constant times exp((β−1/2)T). Taking T=log B−W and κ=exp W places the window [B/κ,B] inside every admissible [A,B]. The factor from shifting the logarithmic endpoint enters the constant and leaves the exponent β−1/2.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass.prime_tail_fixed_ratio_mass_of_zero`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualFilteredLeadingPair](ActualFilteredLeadingPair.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](PrimeOnlyTailCorrection.md)
- Dependency: [D5/S3/Weil/ZeroData/ActualHighZeroFilter](../../ZeroData/ActualHighZeroFilter.md)
