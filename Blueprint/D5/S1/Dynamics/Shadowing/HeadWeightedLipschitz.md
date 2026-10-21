# An Exact Head-Weight Criterion for Lipschitz Shadowing

## Abstract

Lipschitz shadowing for every normalized positive nonincreasing head-weight full shift is equivalent to a cross-head adjacent-depth ratio bound.

On a countable alphabet, prefix weights may depend on the initial symbol. The theorem gives an exact Lipschitz shadowing criterion for every normalized positive nonincreasing family of those weights. Uniform upper and lower envelopes are unnecessary. The existing counterexample answers the unrestricted metric-change question of Goncalves and Silva, arXiv:2603.03200v1, negatively; this result explains the quantitative boundary within its head-weight family.

**Theorem 1.1 (The exact cross-head criterion).**

$$\begin{aligned}\forall w: \operatorname{HeadWeights}(),\\\operatorname{HasLipschitzShadowing}(\operatorname{rawMetric}(w), \operatorname{shift}(1)) \iff \exists C: \mathbb{R}, 0 < C \land\\\forall s t n: \mathbb{N}, 1 \le n \Rightarrow \operatorname{weight}(w, s, n) \le C\operatorname{weight}(w, t, n-1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/HeadWeightedLipschitz.rawMetric_hasLipschitzShadowing_iff_adjacent_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Goncalves and Sofia Meneghel Silva (2026). *Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets*. URL: <https://arxiv.org/abs/2603.03200v1>.

*Commentary.*

For sufficiency, use the actual infinite diagonal splice. A tracing mismatch at depth n telescopes to an edge mismatch at depth m<=n-1. The cross-head comparison followed by antitonicity bounds the tracing error by C times that strict edge error, at every natural time. This supplies constant C and cutoff one, with all symbols and infinite pseudo-orbits quantified.

For necessity, let L and c be proposed positive Lipschitz controls and set C=max(2L,max(2/c,1)). Every weight is at most one, so a violating ratio, with e=weight(t,n-1), gives Ce<1 and hence 2e<c. Depth one and equal heads cannot violate the bound. The existing single-defect infinite pseudo-orbit has strict edge errors below delta=2e and permits no full tracer at radius L delta<=Ce<weight(s,n). Time zero forces the old symbol at position n, while time n forces the inserted symbol. This contradiction establishes necessity without any common tail decay hypothesis.

When UniformBounds are available, HeadWeightedMetric replaces the metric uniformity by the standard product uniformity while keeping exactly the same distance. The theorem therefore gives the same criterion for that compatible product metric. The constant weight family has the discrete metric and is also covered, although it has no uniformly vanishing upper envelope. Thus the raw-metric statement extends beyond the product-uniform subclass.

HeadWeightedMetric supplies the metric, prefix controls and exact infinite defect family; MetricTracing supplies diagonal_mismatch_edge. The cross-head iff is repository-derived content relative to those suppliers. It does not count the existing metric counterexample again or assert a classification of arbitrary compatible metrics, the locally compact variant, publication priority or official external acceptance. The retained Reg mirror preserves the complete original telescopes and records unresolved registration issue #5214.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/HeadWeightedLipschitz.rawMetric_hasLipschitzShadowing_iff_adjacent_ratio`
- Dependency: [D5/S1/Dynamics/Shadowing/HeadWeightedMetric](HeadWeightedMetric.md)
