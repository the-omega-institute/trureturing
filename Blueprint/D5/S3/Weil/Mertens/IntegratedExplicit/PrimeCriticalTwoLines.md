# Subleading zeta phases in critical-width windows

## Abstract

Two-line approximation and joint contacts of the prime tail

**Theorem 1.1 (Approximation after exact removal of the upper line).**

$$\forall beta \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; (\left(\frac{1}{2} < gamma \land gamma < beta\right) \land \left((\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le beta) \land (\forall z \in \mathbb{C},\; \left(\operatorname{NontrivialZero}\left(z\right) \land \operatorname{Re}\left(z\right) < beta\right) \Rightarrow \operatorname{Re}\left(z\right) \le gamma)\right)) \Rightarrow \operatorname{lim}_{t \to +\infty} (\operatorname{exp}\left((1 - gamma) \cdot t\right) \cdot \operatorname{Qtheta}\left(\operatorname{exp}\left(t\right)\right) - \operatorname{exp}\left((beta - gamma) \cdot t\right) \cdot \operatorname{F}\left(beta, \operatorname{phi}\left(t\right), 0\right) - \operatorname{F}\left(gamma, \operatorname{phi}\left(t\right), 0\right)) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalTwoLines.prime_tail_two_line_approx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Write Qϑ for primeTail and Fα(h,u) for the signed line profile phaseProfile Re α h u. The phase φ(t) runs over the actual simultaneous zeta-zero occurrences, counted with multiplicity.

The unaveraged integrated explicit formula splits the complete zero series into the β-line and its exact remainder. On the removed line set the coefficients and replacement coordinates to zero. All remaining coordinates then have real part at most γ. Their γ-line projection agrees termwise with the original projection because γ<β.

At the γ scale the full β-line contribution is exp((β−γ)t)·Fβ(φ(t),0). After its exact subtraction, the maximal-real-part projection gives Fγ(φ(t),0) plus a term tending to zero. The elementary explicit-formula correction and the prime-power error both tend to zero at the same scale. The prime-only arithmetic input is Zhao's equation (14).

The critical strip gives a closed instance at β=2 and γ=1, with both line cuts empty. The line bounds may be attained or unattained.

**Theorem 1.2 (Uniform negative points and positive window mass).**

$$\forall beta \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; \forall W \in \mathbb{R},\; (0 < W \land \left(\left(\frac{1}{2} < gamma \land gamma < beta\right) \land \left((\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le beta) \land (\forall z \in \mathbb{C},\; \left(\operatorname{NontrivialZero}\left(z\right) \land \operatorname{Re}\left(z\right) < beta\right) \Rightarrow \operatorname{Re}\left(z\right) \le gamma)\right)\right)) \Rightarrow \left(((\forall h \in H,\; \exists s \in \operatorname{Icc}\left(0, W\right),\; \operatorname{F}\left(beta, h, -s\right) \le 0) \lor (\forall V \in \mathbb{R},\; W < V \Rightarrow \operatorname{liminf}_{B \to +\infty} \frac{\operatorname{N}\left(B \cdot \operatorname{exp}\left(-V\right), B\right)}{B^{beta - \frac{1}{2}}} \ne 0)) \Rightarrow \left((\forall h \in H,\; \forall s \in \operatorname{Icc}\left(0, W\right),\; \left(\operatorname{F}\left(beta, h, -s\right) = 0 \land (\forall v \in \operatorname{Icc}\left(0, W\right),\; 0 \le \operatorname{F}\left(beta, h, -v\right))\right) \Rightarrow \operatorname{F}\left(gamma, h, -s\right) < 0) \Rightarrow \left(\exists c \in \mathbb{R},\; 0 < c \land (\exists T \in \mathbb{R},\; \forall t \in \mathbb{R},\; T \le t \Rightarrow \left((\exists u \in \operatorname{Icc}\left(t - W, t\right),\; \operatorname{exp}\left((1 - gamma) \cdot u\right) \cdot \operatorname{Qtheta}\left(\operatorname{exp}\left(u\right)\right) \le -c) \land 0 < \operatorname{N}\left(\operatorname{exp}\left(t\right) \cdot \operatorname{exp}\left(-W\right), \operatorname{exp}\left(t\right)\right)\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalTwoLines.prime_tail_negative_windows_of_two_line_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N(A,B) be the integral of max(−Qϑ(x),0)/√x from A to B. Let H be the closure of the actual simultaneous phase orbit φ. At width W>0, a contact is a pair (h,s) in H×[0,W] where Fβ(h,−s)=0 and the whole first profile is nonnegative over the lag interval. Assume Fγ(h,−s)<0 at every such pair.

The first profile must take a nonpositive value in each phase window. This holds if every wider window has nonzero lower limit of the normalized mass. Indeed, a phase strictly positive throughout [0,W] stays positive after a short extension at lag W. Its extended phase window has zero mass. The fixed-width cluster theorem gives an actual cluster value of zero for that wider width, hence a zero lower limit by eventual nonnegativity.

The first-profile minimizers form a compact graph in H×[0,W]. The graph is cut out by the closed comparison inequalities with every other lag. At a minimizing pair, Fβ≤0, and equality activates the strict contact condition. The maximum of min(Fβ,Fγ) on the graph is therefore −d<0. The same graph supplies a finite upper bound for Fγ.

Apply this graph estimate at φ(t) and put u=t−s at the chosen minimizing lag. If Fβ≤−d, the growing factor exp((β−γ)u) makes it dominate the upper bound for Fγ. If Fγ≤−d, the leading term is nonpositive. As u≥t−W, one threshold makes the γ-scale approximation error smaller than d/2 throughout all later windows. Thus there is a point in each such window with γ-normalized tail at most −d/2. Continuity of the tail makes the negative-part integral positive even when the selected point is an endpoint.

At an attained maximal real part β>1/2, the critical-width theorem supplies exactly the wider-width premise at W=W*. Thus arbitrarily late zero-mass critical windows force a joint contact with Fγ≥0. The arithmetic gap and the joint contact sign remain hypotheses.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalTwoLines.prime_tail_negative_windows_of_two_line_contact`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalTwoLines.prime_tail_two_line_approx`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster](PrimePhaseCluster.md)
