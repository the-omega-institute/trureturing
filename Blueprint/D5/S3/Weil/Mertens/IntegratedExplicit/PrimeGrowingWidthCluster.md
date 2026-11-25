# Growing logarithmic widths

## Abstract

Cluster values for growing prime-tail windows

**Definition 1.1 (Exponentially weighted infinite phase window).**

$$\forall r \in (\mathbb{C} \to \mathbb{R}),\; \forall beta \in \mathbb{R},\; \forall h \in \mathbb{T}^{\mathbb{N}},\; I_{\infty}(r, beta, h) = \int_{\operatorname{Ioi}\left(0\right)} \operatorname{exp}\left(-\left(beta - \frac{1}{2}\right) \cdot s\right) \cdot \operatorname{max}\left(-\operatorname{F}\left(r, beta, h, -s\right), 0\right) ds$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.phaseWindowInfinite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile F uses the coefficients on the line r(ρ)=β. Each coordinate of h is indexed by an actual zero occurrence, including multiplicities. The integral uses Lebesgue measure on s>0. Including s=0 gives the same value.

**Theorem 1.2 (Uniform left-endpoint bound).**

$$\forall beta \in \mathbb{R},\; \frac{1}{2} < beta \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le beta\right) \Rightarrow \left(\exists K \in \mathbb{R},\; 0 \le K \land \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \operatorname{Eventually}\left((\lambda B:\mathbb{R} \mapsto \forall a \in \mathbb{R},\; \left(2 \le a \land a \le B\right) \Rightarrow \left(\left|\frac{\operatorname{N}\left(a, B\right)}{B^{beta - \frac{1}{2}}} - I_{\infty}(Re, beta, \operatorname{phi}\left(\operatorname{log}\left(B\right)\right))\right| \le epsilon + K \cdot \frac{a}{B}^{beta - \frac{1}{2}} \land \frac{\operatorname{N}\left(a, B\right)}{B^{beta - \frac{1}{2}}} - I_{\infty}(Re, beta, \operatorname{phi}\left(\operatorname{log}\left(B\right)\right)) \le epsilon\right)), atTop\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.prime_tail_window_extent_bound_of_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Write Qϑ(x) for the actual prime-only tail, the integral of (ϑ(u)−u)/u² over u>x from Zhao's equation (14). The mass N(a,B) integrates max(−Qϑ(x),0)/√x from a to B. Put p=β−1/2 and let φ be the simultaneous phase orbit of the actual zero occurrences. The threshold in B can depend on ε and β and applies to every a∈[2,B].

Let X≥2 be a fixed threshold beyond which the arithmetic density is bounded by C x^(p−1), and write C₀=N(2,X). A prefix ending below X has mass at most C₀. Above X, integrating the power bound gives N(2,a)≤C₀+(C/p)(a^p−X^p). Since a≥2, K=C₀/2^p+C/p bounds N(2,a)/a^p in both cases.

For fixed L≥0 and large B, the rightmost window starts at D=B exp(−L). The normalized prefix up to D is bounded by K exp(−pL). The fixed-width transfer approximates the normalized mass from D to B by the truncated phase integral at φ(log B). If S is the sum of the norms of the complete-tail coefficients, the omitted phase integral is bounded by (S/p) exp(−pL), uniformly in the phase. Taking L large and then B large makes the cumulative residual arbitrarily small. This argument gives eventual control for each ε.

Subtract N(2,a)/B^p from the cumulative normalized mass. This subtraction can increase the lower error by at most K(a/B)^p. The upper error stays bounded by ε because the removed mass is nonnegative.

**Theorem 1.3 (Exact cluster values for moving left endpoints).**

$$\forall beta \in \mathbb{R},\; \frac{1}{2} < beta \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le beta\right) \Rightarrow \left(\forall A \in (\mathbb{R} \to \mathbb{R}),\; \operatorname{Eventually}\left((\lambda B:\mathbb{R} \mapsto 2 \le \operatorname{A}\left(B\right) \land \operatorname{A}\left(B\right) \le B), atTop\right) \Rightarrow \left(\operatorname{Tendsto}\left((\lambda B:\mathbb{R} \mapsto \operatorname{log}\left(\frac{B}{\operatorname{A}\left(B\right)}\right)), atTop, atTop\right) \Rightarrow \left(\forall y \in \mathbb{R},\; \operatorname{MapClusterPt}\left(y, atTop, (\lambda B:\mathbb{R} \mapsto \frac{\operatorname{N}\left(\operatorname{A}\left(B\right), B\right)}{B^{beta - \frac{1}{2}}})\right) \Leftrightarrow \left(\exists h \in \mathbb{T}^{\mathbb{N}},\; h \in \operatorname{closure}\left(\operatorname{range}\left(phi\right)\right) \land y = I_{\infty}(Re, beta, h)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.prime_tail_growing_width_cluster_iff_of_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let H be the closure of φ. The finite-width phase integrals are continuous, and the uniform exponential bound on their tails makes the infinite phase integral continuous as well.

When log(B/A(B)) tends to infinity, the endpoint factor (A(B)/B)^p tends to zero. The uniform bound therefore transfers the cluster values from the phase integral evaluated at φ(log B) to the moving mass. Forward recurrence of φ and compactness of H give both directions of the cluster equivalence. If the β-line is empty, the phase image is {0}. In particular β=1 is an admissible upper bound and its line is empty.

Bugajewski, Diagana and Mahop study integrable-kernel convolution of asymptotically almost periodic functions in Theorem 3.3 and the exponential kernel in §4 (doi:10.4171/zaa/1292). Bingham and Gashi's logarithmic moving averages use logarithmic summability normalization (arXiv:1408.1301).

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.phaseWindowInfinite`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.prime_tail_growing_width_cluster_iff_of_upper_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.prime_tail_window_extent_bound_of_upper_bound`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedCriticalWidth](PrimeAttainedCriticalWidth.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster](PrimePhaseCluster.md)
