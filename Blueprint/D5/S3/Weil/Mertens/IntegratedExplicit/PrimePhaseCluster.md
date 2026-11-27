# The actual zeta phase orbit at a real-part upper bound

## Abstract

Cluster values of normalized prime-tail window mass

**Definition 1.1 (Simultaneous zero phases).**

$$\forall t \in \mathbb{R},\; \forall k \in \mathbb{N},\; \operatorname{phi}\left(t, k\right) = \operatorname{exp}\left(i \cdot \operatorname{gamma}\left(k\right) \cdot t\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.phaseOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index k runs over all actual zero occurrences via actualOccurrenceEquiv. Write γ(k)=Im(actualZero(k)). The coordinates are unit complex numbers.

**Definition 1.2 (Coefficients on the selected line).**

$$\forall r \in (\mathbb{C} \to \mathbb{R}),\; \forall beta \in \mathbb{R},\; \forall k \in \mathbb{N},\; \operatorname{a}\left(r, beta, k\right) = \operatorname{ite}\left(\operatorname{r}\left(\operatorname{actualZero}\left(k\right)\right) = beta, \operatorname{c}\left(k\right), 0\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.rightmostCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-part map r is fixed to Re in the theorem. The coefficient c(k) is actualCoeff(k), the reciprocal of ρ(k)(1−ρ(k)) at occurrence k.

**Definition 1.3 (The real complete-tail profile).**

$$\forall r \in (\mathbb{C} \to \mathbb{R}),\; \forall beta \in \mathbb{R},\; \forall h \in \mathbb{T}^{\mathbb{N}},\; \forall u \in \mathbb{R},\; \operatorname{F}\left(r, beta, h, u\right) = -\operatorname{Re}\left(\sum_{k \in \mathbb{N}} \operatorname{a}\left(r, beta, k\right) \cdot \operatorname{h}\left(k\right) \cdot \operatorname{phi}\left(u, k\right)\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.phaseProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The minus sign comes from the actual integrated explicit formula. Norms of the original coefficients give one summable bound for all phases and lags.

**Definition 1.4 (Weighted negative part over a log window).**

$$\forall r \in (\mathbb{C} \to \mathbb{R}),\; \forall beta \in \mathbb{R},\; \forall W \in \mathbb{R},\; \forall h \in \mathbb{T}^{\mathbb{N}},\; \operatorname{I}\left(r, beta, W, h\right) = \int_{0}^{W} \operatorname{exp}\left(-\left(beta - \frac{1}{2}\right) \cdot s\right) \cdot \operatorname{max}\left(-\operatorname{F}\left(r, beta, h, -s\right), 0\right) ds$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.phaseWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real variable s runs backwards from the right endpoint in logarithmic coordinates.

**Theorem 1.5 (Exact cluster-set equivalence).**

$$\forall beta \in \mathbb{R},\; \frac{1}{2} < beta \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le beta\right) \Rightarrow \left(\forall W \in \mathbb{R},\; 0 \le W \Rightarrow \left(\forall y \in \mathbb{R},\; \operatorname{MapClusterPt}\left(y, atTop, (\lambda B:\mathbb{R} \mapsto \frac{\operatorname{N}\left(B \cdot \operatorname{exp}\left(-W\right), B\right)}{B^{beta - \frac{1}{2}}})\right) \Leftrightarrow \left(\exists h \in \mathbb{T}^{\mathbb{N}},\; h \in \operatorname{closure}\left(\operatorname{range}\left(phi\right)\right) \land y = \operatorname{I}\left(Re, beta, W, h\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.prime_tail_mass_cluster_iff_of_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let N(A,B) denote the Chapter 31 interval integral from A to B of max(−Qϑ(x),0)/√x. Here Qϑ is primeTail, the integral of (ϑ(u)−u)/u² over u>x, with each prime counted once in ϑ. Cluster means MapClusterPt along the real atTop filter. H is the closure of the range of the simultaneous real phase orbit.

For the Chapter 31 application, take β to be the real part of a nontrivial zero attaining the maximum above one half and take W>0. If the β-line cut is empty, all cut coefficients vanish. The identity φ(0) belongs to H, so the phase image and cluster set both equal {0}. At W=0 both interval integrals vanish, giving the same singleton.

The product of circles is compact. Apply mapClusterPt_one_atTop_pow to φ(1). Multiplication by φ(t) sends those powers to φ(t+n), and t+n tends to infinity along the natural numbers. Thus every orbit point belongs to the closed set of forward cluster points. The reverse inclusion follows from containment in H.

The common summable coefficient bound gives joint continuity in phase and lag. Parametric interval integration gives continuity of I. Its image of H is compact and hence closed. The continuous image of the real line under φ and its closure are connected, so the functional image is a compact interval.

Put t=log B and p=β−1/2. The substitution x=exp(t−s) gives the exact normalized integral with weight exp(−ps) and signed input exp((1−β)(t−s))·Qϑ(exp(t−s)). On the orbit the profile is the negative real part of the actual β-line series at t−s. The complete-tail approximation and normalized prime-power error bound the difference of the signed inputs by δ on all of [t−W,t] once t is sufficiently large. The 1-Lipschitz negative part bounds the window error by δ times the integral of exp(−ps).

The vanishing window error preserves cluster values by the triangle inequality in frequent metric balls. Continuity and forward recurrence yield every value in the phase image, and closedness of that image contains every cluster value of the phase windows. Exponentiation and logarithm preserve the real cofinal limit.

Kaczorowski and Ramaré discuss translation hulls in Section 4 of Almost periodicity of some error terms in prime number theory (doi:10.4064/aa106-3-6). Lee et al. relate the uniform translation hull to the Bohr compactification in Appendix A.2 of arXiv:1907.07017.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.phaseOrbit`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.phaseProfile`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.phaseWindow`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.prime_tail_mass_cluster_iff_of_upper_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster.rightmostCoeff`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows](PrimeAttainedShortWindows.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean](RHPrimeWindowMean.md)
