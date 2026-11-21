# Growing logarithmic widths

## Abstract

Cluster values for growing prime-tail windows

**Definition 1.1 (Exponentially weighted infinite phase window).**

$$\forall r \in (\mathbb{C} \to \mathbb{R}),\; \forall beta \in \mathbb{R},\; \forall h \in \mathbb{T}^{\mathbb{N}},\; I_{\infty}(r, beta, h) = \int_{\operatorname{Ioi}\left(0\right)} \operatorname{exp}\left(-\left(beta - \frac{1}{2}\right) \cdot s\right) \cdot \operatorname{max}\left(-\operatorname{F}\left(r, beta, h, -s\right), 0\right) ds$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.phaseWindowInfinite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile F uses the coefficients on the line r(ρ)=β. Each coordinate of h is indexed by an actual zero occurrence, including multiplicities. The integral uses Lebesgue measure on s>0. Including s=0 gives the same value.

**Theorem 1.2 (Exact cluster values for moving left endpoints).**

$$\forall beta \in \mathbb{R},\; \frac{1}{2} < beta \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le beta\right) \Rightarrow \left(\forall A \in (\mathbb{R} \to \mathbb{R}),\; \operatorname{Eventually}\left((\lambda B:\mathbb{R} \mapsto 2 \le \operatorname{A}\left(B\right) \land \operatorname{A}\left(B\right) \le B), atTop\right) \Rightarrow \left(\operatorname{Tendsto}\left((\lambda B:\mathbb{R} \mapsto \operatorname{log}\left(\frac{B}{\operatorname{A}\left(B\right)}\right)), atTop, atTop\right) \Rightarrow \left(\forall y \in \mathbb{R},\; \operatorname{MapClusterPt}\left(y, atTop, (\lambda B:\mathbb{R} \mapsto \frac{\operatorname{N}\left(\operatorname{A}\left(B\right), B\right)}{B^{beta - \frac{1}{2}}})\right) \Leftrightarrow \left(\exists h \in \mathbb{T}^{\mathbb{N}},\; h \in \operatorname{closure}\left(\operatorname{range}\left(phi\right)\right) \land y = I_{\infty}(Re, beta, h)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.prime_tail_growing_width_cluster_iff_of_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Write Qϑ(x) for the actual prime-only tail, the integral of (ϑ(u)−u)/u² over u>x from Zhao's equation (14). The mass N(A,B) integrates max(−Qϑ(x),0)/√x from A to B. The variable B tends to +∞ through real values. The left endpoint A(B) is chosen pointwise. The constant choice A(B)=2 gives the cumulative mass.

Let H be the closure of the simultaneous orbit φ of the actual zero occurrences, and put p=β−1/2>0. If S is the sum of the norms of the complete-tail coefficients, the infinite phase integral minus its truncation at L≥0 lies between zero and (S/p) exp(−pL) for every phase. Thus the continuous finite-width integrals converge uniformly, and the infinite phase integral is continuous.

Fix L≥0 and put D=B exp(−L). Eventually A(B)≤D≤B. Let X≥2 be a fixed threshold beyond which the arithmetic density is bounded by C x^(p−1). For B with D≥X, split the added segment [A(B),D] at max(A(B),X). Its early contribution is at most C₀=N(2,X). Integrating the power bound on the rest and dividing by B^p bounds the normalized added mass by (C/p) exp(−pL)+C₀/B^p, uniformly in the admissible left endpoint.

At fixed L the logarithmic change of variables and the signed-input estimate approximate the normalized rightmost window by the finite phase integral at φ(log B). Taking L large and then B large makes the moving mass differ from the infinite integral at that very phase by a quantity tending to zero. Forward recurrence of φ and compactness of H give both directions of the cluster equivalence. If the β-line is empty, the phase image is {0}. In particular β=1 is an admissible upper bound and its line is empty.

Bugajewski, Diagana and Mahop study integrable-kernel convolution of asymptotically almost periodic functions in Theorem 3.3 and the exponential kernel in §4 (doi:10.4171/zaa/1292). Bingham and Gashi's logarithmic moving averages use logarithmic summability normalization (arXiv:1408.1301).

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.phaseWindowInfinite`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster.prime_tail_growing_width_cluster_iff_of_upper_bound`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedCriticalWidth](PrimeAttainedCriticalWidth.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster](PrimePhaseCluster.md)
