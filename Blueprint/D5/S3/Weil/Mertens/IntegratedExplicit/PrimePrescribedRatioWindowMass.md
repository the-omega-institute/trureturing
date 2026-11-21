# An unattained zeta abscissa

## Abstract

Prime-tail negative mass on prescribed-ratio windows

**Theorem 1.1 (Every prescribed ratio and every strict surplus exponent).**

$$\left(\forall rho \in \mathbb{C},\; \operatorname{NontrivialZero}\left(rho\right) \Rightarrow \operatorname{Re}\left(rho\right) < Theta\right) \Rightarrow \left(\forall kappa \in \mathbb{R},\; \forall sigma \in \mathbb{R},\; 1 < kappa \Rightarrow \left(\frac{1}{2} < sigma \Rightarrow \left(sigma < Theta \Rightarrow \left(\exists c \in \mathbb{R},\; \exists S \in \mathbb{R},\; 0 < c \land \left(\forall B \in \mathbb{R},\; S \le B \Rightarrow \left(\forall A \in \mathbb{R},\; 2 \le A \Rightarrow \left(kappa \cdot A \le B \Rightarrow c \cdot B^{sigma - \frac{1}{2}} \le \operatorname{N}\left(A, B\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePrescribedRatioWindowMass.prime_tail_prescribed_ratio_mass_of_unattained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let Θ be the supremum of the real parts of the nontrivial zeros of the Riemann zeta function, and assume every such zero has real part strictly below Θ. The exponent range 1/2 < σ < Θ entails Θ > 1/2. Write Qθ(x) for the integral of (θ(t)−t)/t² above x, as in Zhao's equation (14), and N(A,B) for the integral of max(−Qθ(x),0)/√x from A to B.

For the prescribed ratio κ, set W=log κ and h=W/2. Choose a probability filter supported on [0,h] that retains a conjugate pair with real part β and positive ordinate γ > 4π/h. Its other surviving zeros have real parts at most b, with σ ≤ b < β. If P=2π/γ, then h+2P<W.

The negative filtered complete Chebyshev tail has a cosine term with positive amplitude at scale exp((β−1)t). Its error divided by that scale decays with exponent b−β. Every interval [T,T+2P] contains a subinterval of length π/(3γ) on which the cosine is at least one half. For all sufficiently large T, the signed integral over this subinterval is bounded below by a positive constant times exp((β−1)T). Every translate by a point in the filter support lies in [T,T+W]. Exchanging the integrals then bounds the signed average by the unaveraged negative mass of the complete tail on that log interval.

The substitution x=exp(t) and the inequality Qθ≤Q transfer the log mass to the weighted prime-only mass, giving a positive constant times exp((β−1/2)T). With T=log B−W, the interval [exp T,exp(T+W)] is [B/κ,B], which is contained in [A,B] whenever κA≤B. The shift of the log endpoint changes only the constant. Since B≥1 and β>σ, the power B^(β−1/2) is at least B^(σ−1/2). The resulting coefficient and cutoff are chosen before either endpoint.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePrescribedRatioWindowMass.prime_tail_prescribed_ratio_mass_of_unattained`
- Dependency: [D5/S3/Arith/Robin/Analytic/ActualUnattainedAbscissaFilter](../../../Arith/Robin/Analytic/ActualUnattainedAbscissaFilter.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass](PrimeFixedRatioWindowMass.md)
