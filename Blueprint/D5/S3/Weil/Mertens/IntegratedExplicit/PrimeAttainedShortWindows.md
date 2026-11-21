# Positive prime-tail windows at an attained zeta abscissa

## Abstract

Positive prime-tail windows at an attained zeta abscissa

**Theorem 1.1 (Recurring whole windows of positivity).**

$$\forall rho \in \mathbb{C},\; \operatorname{NontrivialZero}\left(rho\right) \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(rho\right) \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le \operatorname{Re}\left(rho\right)\right) \Rightarrow \left(\exists R \in \mathbb{R},\; \exists K \in \mathbb{R},\; \exists S \in \mathbb{R},\; 1 < R \land \left(1 \le K \land \left(2 \le S \land \left(\forall X \in \mathbb{R},\; S \le X \Rightarrow \left(\exists A \in \operatorname{Icc}\left(X, K \cdot X\right),\; \left(\forall x \in \operatorname{Icc}\left(A, R \cdot A\right),\; 0 < \operatorname{Qtheta}\left(x\right)\right) \land \left(\forall k \in \operatorname{Icc}\left(1, R\right),\; \operatorname{N}\left(A, k \cdot A\right) = 0\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows.prime_tail_positive_short_windows_of_attained_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let Qθ(x) be the integral of (θ(u)−u)/u² over u>x, with θ summing log p once for each prime p≤u. This is the tail in Zhao's equation (14). Let N(A,B) be the integral of max(−Qθ(x),0)/√x from A to B, and let Q be the tail defined using ψ in place of θ.

Choose the positive-ordinate zero in the conjugate pair of the supplied zero. Write β for its real part and γ for its positive ordinate. A compact forward probability filter preserves this pair and cancels all other modes right of a cutoff strictly between one half and β. The resulting leading cosine gives a positive value of Q(exp u) at some u in every sufficiently late log window of length W=2π/γ+h, where h is the filter support bound. Since β<1, the normalized value exp((1−β)u)Q(exp u) exceeds a single c>0 at these peaks.

The maximal real-part projection gives a uniformly continuous approximant to the normalized unfiltered tail. It keeps all modes with real part β. Absolute summability controls the strict lower modes even when their real parts approach β. The root-scale prime-power correction tends to two, so after normalization at β>1/2 the correction tends to zero. The normalized prime-only tail therefore has the same approximant and retains a positive margin at each sufficiently late peak.

Choose δ>0 so that the approximant moves by less than c/4 over distances less than δ. The margin and the approximation errors at both points give positivity for every v in [u,u+δ/2]. Starting at log X and exponentiating gives A=exp u, K=exp W, and R=exp(δ/2). Positivity holds at both endpoints. For each ratio k in [1,R], the integrand of N(A,kA) vanishes on the entire interval.

Kaczorowski's bounded-gap level crossings and discussion of the attained case give a precedent for the almost-periodic method on different observables. See pp. 232 and 234, DOI 10.4064/aa-57-3-231-244.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows.prime_tail_positive_short_windows_of_attained_zero`
- Dependency: [D5/S3/Analytic/Laplace/MaximalRealPartProjection](../../../Analytic/Laplace/MaximalRealPartProjection.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ActualUnattainedChebyshevWindows](../../../Arith/Robin/Analytic/ActualUnattainedChebyshevWindows.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](PrimeOnlyTailCorrection.md)
