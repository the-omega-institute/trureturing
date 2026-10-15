# A Negative Product-Metric Stability Answer

## Abstract

Uniform equivalence preserves ordinary shadowing of the natural full product shift while a concrete head-dependent metric loses every Lipschitz tracing constant.

Let X be the entire product N^N and sigma(x)(j)=x(j+1). For unequal sequences let n=firstDiff(x,y), a(n)=(1/2)^n and b(n)=(1/2)^(n*n). Give equal sequences distance zero. Give unequal sequences distance a(n) if both heads are one, and b(n) otherwise. When heads differ, n=0 and both weights are one. This metric depends on the common head and lies outside the globally symbol-independent prefix class of Definition 3.3 in Goncalves and Silva, arXiv:2603.03200v1. The unrestricted Section 3 question on printed/PDF p.6 permits it. The statements below are deductions answering that question, not conclusions attributed to the paper.

**Theorem 1.1 (The exact displayed distance).**

$$\begin{aligned}\forall x: \mathbb{N} \to \mathbb{N},\forall y: \mathbb{N} \to \mathbb{N},\operatorname{dist}(x, y) = \operatorname{if}(x = y, 0, \operatorname{if}(\operatorname{apply}(x, 0) = 1 \land \operatorname{apply}(y, 0) = 1, \operatorname{a}(\operatorname{firstDiff}(x, y)), \operatorname{b}(\operatorname{firstDiff}(x, y))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.distance_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Goncalves and Sofia Meneghel Silva (2026). *Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets*. URL: <https://arxiv.org/abs/2603.03200v1>.

*Commentary.*

The HeadWeights constructor agrees with both branches, including pairs whose heads differ and the zero diagonal. Its positive antitone weights make an actual MetricSpace, with the strong triangle inequality.

**Theorem 1.2 (The exact discrete product uniformity).**

$$\begin{aligned}\operatorname{uniformSpace}(metric) = \operatorname{PiUniformSpace}(\mathbb{N})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.product_uniformity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Goncalves and Sofia Meneghel Silva (2026). *Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets*. URL: <https://arxiv.org/abs/2603.03200v1>.

*Commentary.*

For every unequal pair b(n)<=d(x,y)<=a(n); equal pairs have zero distance. Strict distance<b(N) forces agreement through N. The raw weighted metric and PiNat.metricSpaceNatNat have both uniformly continuous identity maps on all symbols and all sequences. The aligned metric has precisely the standard product uniform structure and topology, not just a continuous identity on a binary subset.

**Theorem 1.3 (Full infinite ordinary shadowing).**

$$\begin{aligned}\operatorname{MetricHasShadowing}(sigma)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.hasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Goncalves and Sofia Meneghel Silva (2026). *Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets*. URL: <https://arxiv.org/abs/2603.03200v1>.

*Commentary.*

Choose a(N)<epsilon and delta=b(N)>0. Errors below delta force overlap through coordinate N. The infinite diagonal splice y(k)=z(k)(0) agrees with z(i) through N+1 at every time i, and its weighted tail distance is below epsilon. The metric entourage bridge also identifies this with the existing UniformHasShadowing contract; compact finite-cover shadowing is not used.

**Theorem 1.4 (Every proposed pair of constants fails).**

$$\begin{aligned}\forall L: \mathbb{R},\\\forall c: \mathbb{R},\\0 < L \Rightarrow\\0 < c \Rightarrow\\\exists d, 0 < d \land d \le c \land \exists z: \mathbb{N} \to \mathbb{N} \to \mathbb{N},\operatorname{MetricPseudoOrbit}(sigma, d, z) \land \forall y: \mathbb{N} \to \mathbb{N},\neg \operatorname{MetricTraces}(sigma, Ld, z, y)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.bad_pseudoOrbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Goncalves and Sofia Meneghel Silva (2026). *Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets*. URL: <https://arxiv.org/abs/2603.03200v1>.

*Commentary.*

Choose N>=4 with a(N)<min(c/2,1/(2L)). The inequality (N-1)^2>=2N gives b(N-1)<=a(N)^2, so delta=2b(N-1)>0 satisfies delta<=c and L delta<a(N). Use head one at time zero and a sole one at coordinate N-1 at time one, then follow the exact infinite orbit. The only nonzero error is b(N-1)<delta. Time zero forces y(N)=0; time N has observed head one and tracer head zero, hence distance one. This contradicts every full strict L delta tracer.

**Theorem 1.5 (Uniform metric stability is false).**

$$\begin{aligned}\neg \operatorname{productmetricstability}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Goncalves and Sofia Meneghel Silva (2026). *Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets*. URL: <https://arxiv.org/abs/2603.03200v1>.

*Commentary.*

product_metric_stability quantifies over every actual MetricSpace m on N^N: if both identities between m and the standard product metric are uniformly continuous, ordinary strict metric shadowing would imply Lipschitz shadowing. The concrete metric supplies both identities and ordinary shadowing, but bad_pseudoOrbit disproves Lipschitz shadowing with the full positive-L, positive-cutoff, infinite-sequence and all-time quantifiers.

**Theorem 1.6 (What changes with the metric).**

$$\begin{aligned}(\forall x: \mathbb{N} \to \mathbb{N},\forall y: \mathbb{N} \to \mathbb{N},\operatorname{dist}(x, y) = \operatorname{if}(x = y, 0, \operatorname{if}(\operatorname{apply}(x, 0) = 1 \land \operatorname{apply}(y, 0) = 1, \operatorname{a}(\operatorname{firstDiff}(x, y)), \operatorname{b}(\operatorname{firstDiff}(x, y))))) \land\\(\forall x: \mathbb{N} \to \mathbb{N},\forall y: \mathbb{N} \to \mathbb{N},x \neq y \Rightarrow\operatorname{b}(\operatorname{firstDiff}(x, y)) \le \operatorname{dist}(x, y) \land \operatorname{dist}(x, y) \le \operatorname{a}(\operatorname{firstDiff}(x, y))) \land\\(\forall x: \mathbb{N} \to \mathbb{N},\forall y: \mathbb{N} \to \mathbb{N},\forall z: \mathbb{N} \to \mathbb{N},\operatorname{dist}(x, z) \le \operatorname{max}(\operatorname{dist}(x, y), \operatorname{dist}(y, z))) \land\\(\operatorname{UniformContinuous}(metric, metricSpaceNatNat, id) \land \operatorname{UniformContinuous}(metricSpaceNatNat, metric, id)) \land\\(\operatorname{uniformSpace}(metric) = \operatorname{PiUniformSpace}(\mathbb{N})) \land\\(\operatorname{topology}(metric) = \operatorname{PiTopology}(\mathbb{N})) \land\\\operatorname{Continuous}(sigma) \land \operatorname{UniformHasShadowing}(sigma) \land\\\operatorname{MetricHasShadowing}(metricSpaceNatNat, sigma) \land \operatorname{HasLipschitzShadowing}(metricSpaceNatNat, sigma) \land \operatorname{MetricHasShadowing}(metric, sigma) \land \neg \operatorname{HasLipschitzShadowing}(metric, sigma)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.metric_change_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Goncalves and Sofia Meneghel Silva (2026). *Shadowing and Lipschitz Shadowing in Symbolic Dynamics: Finite vs. Infinite Alphabets*. URL: <https://arxiv.org/abs/2603.03200v1>.

*Commentary.*

The certificate includes the exact displayed distance, sandwich bounds, strong triangle inequality, both uniform identity maps, the exact discrete product uniformity and topology, shift continuity and uniform shadowing. The standard product metric has Lipschitz shadowing with L=1, using the diagonal mismatch telescope and the half-error bound. Both metrics have ordinary shadowing; the new metric loses Lipschitz shadowing despite the identical uniform structure. N^N is not locally compact, whereas Definition 2.1 uses local compactness in preliminary Deaconu--Renault terminology. This conclusion concerns the literal unrestricted Section 3 question. It does not assert the separately scoped locally compact variant, a general ratio classification, official acceptance, or global uniqueness from the bounded literature search.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.bad_pseudoOrbit`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.distance_formula`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.hasShadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.metric_change_counterexample`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.product_uniformity`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.result`
- Dependency: [D5/S1/Dynamics/Shadowing/HeadWeightedMetric](HeadWeightedMetric.md)
