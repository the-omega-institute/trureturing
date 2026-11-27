# The endpoint-scale upper bound

## Abstract

Prime-tail negative mass at an unattained zeta abscissa

**Theorem 1.1 (Vanishing normalized mass over all real windows).**

$$\frac{1}{2} < Theta \Rightarrow \left(\left(\forall rho \in \mathbb{C},\; \operatorname{NontrivialZero}\left(rho\right) \Rightarrow \operatorname{Re}\left(rho\right) < Theta\right) \Rightarrow \operatorname{Tendsto}\left((\lambda B:\mathbb{R} \mapsto \frac{\operatorname{N}\left(2, B\right)}{B^{Theta - \frac{1}{2}}}), atTop, \operatorname{nhds}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeUnattainedEndpointMass.prime_tail_endpoint_mass_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let Θ be the supremum of the real parts of the nontrivial zeta zeros. Write Qθ(x) for the integral of (θ(u)−u)/u² over u>x, the tail in Zhao’s equation (14), where θ sums log p once per prime p≤u. Write N(A,B) for the integral of max(−Qθ(x),0)/√x from A to B.

The real part of each actual zero is bounded above by Θ. The normalized complete Chebyshev tail differs from the negative real part of the maximal-line series by a quantity tending to zero. Absolute summability controls the lower terms even when their real parts approach Θ. Strict unattainment makes every maximal-line term zero. The prime-power correction vanishes under the same normalization since Θ>1/2. Substituting t=log x yields x^(1−Θ) Qθ(x)→0 for real x→+∞. This includes Θ=1.

Set p=Θ−1/2>0. For any ε>0, choose X≥2 such that the mass integrand is at most (ε/2)p x^(p−1) for x≥X. For B≥X, integrating this power bounds N(X,B) by (ε/2)(B^p−X^p). The fixed initial mass N(2,X) divided by B^p tends to zero. Nonnegativity then gives the limit.

For each B≥2, nonnegativity also makes N(2,B)/B^p the maximum of N(A,B)/B^p over all real A with 2≤A≤B. The same cutoff in B controls all such A, including every window ratio.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeUnattainedEndpointMass.prime_tail_endpoint_mass_tendsto_zero`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows](PrimeAttainedShortWindows.md)
