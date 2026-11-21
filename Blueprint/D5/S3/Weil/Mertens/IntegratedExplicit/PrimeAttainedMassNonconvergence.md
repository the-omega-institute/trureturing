# Fixed-ratio windows at an attained zeta abscissa

## Abstract

Nonconvergence of normalized prime-tail mass

**Theorem 1.1 (Exclusion of every finite limit).**

$$\forall rho \in \mathbb{C},\; \operatorname{NontrivialZero}\left(rho\right) \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(rho\right) \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le \operatorname{Re}\left(rho\right)\right) \Rightarrow \left(\forall kappa \in \mathbb{R},\; \forall L \in \mathbb{R},\; 1 < kappa \Rightarrow \neg \operatorname{Tendsto}\left((\lambda B:\mathbb{R} \mapsto \frac{\operatorname{N}\left(\frac{B}{kappa}, B\right)}{B^{\operatorname{Re}\left(rho\right) - \frac{1}{2}}}), atTop, \operatorname{nhds}\left(L\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedMassNonconvergence.prime_tail_mass_no_finite_limit_of_attained_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let Qθ(x) integrate (θ(u)−u)/u² over u>x, where θ sums log p once per prime p≤u. This prime-only tail appears in Zhao's equation (14). Define N(A,B) by integrating max(−Qθ(x),0)/√x from A to B. For β=Re ρ and p=β−1/2, put Mκ(B)=N(B/κ,B)/B^p with B real.

Assume Mκ tends to L. The recurring positive-tail windows give a ratio R>1. Take λ=min(κ,R), q=κ^(−p), and r=λ^(−p). The nonnegative density gives 0≤Mλ≤Mκ for sufficiently large B. Splitting [B/(κλ),B] at B/κ and at B/λ gives Mλ(B)−q Mλ(B/κ)=Mκ(B)−r Mκ(B/λ). The right-hand side tends to (1−r)L.

Set C=(1−r)L/(1−q) and e=Mλ−C. The residual e(B)−q e(B/κ) tends to zero, and |e| is eventually bounded by some M. Given ε>0, the residual is eventually bounded in absolute value by ε(1−q)/2. Since B/κ tends to infinity with B, induction gives, for each fixed n and all sufficiently large B, |e(B)|≤q^n M+(ε/2)(1−q^n). Choosing n with q^n M<ε/2 gives Mλ→C.

The recurring zero-mass windows have right endpoints B=λA arbitrarily far out. Thus C=0 and, since r<1, L=0. The lower bound from the supplied zero gives a ratio k and a constant c>0. Choose m with κ^m≥k. Repeated splitting expresses M at ratio κ^m as a sum of the m terms q^j Mκ(B/κ^j) for 0≤j<m, each tending to zero. The lower bound gives M at ratio κ^m at least c for every sufficiently large B, a contradiction.

Bingham and Gashi use a geometric expansion for discrete logarithmic means in Theorem 1 and equations (2.3)–(2.4) of Logarithmic moving averages (arXiv:1408.1301). Here the recurrence comes from interval additivity of the continuous prime-tail mass.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedMassNonconvergence.prime_tail_mass_no_finite_limit_of_attained_zero`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows](PrimeAttainedShortWindows.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass](PrimeFixedRatioWindowMass.md)
