# Head-Weighted Product Metrics

## Abstract

Head-dependent ultrametrics with uniform cylinder control shadow infinite pseudo-orbits; a single defect obstructs quantitative tracing.

A HeadWeights object w consists of w(s,n)>0, nonincreasing in n, with w(s,0)=1 for every natural symbol s. For unequal x,y set d(x,y)=w(x(0),firstDiff(x,y)); on equality set d=0. Differing heads have first difference zero and distance one, so symmetry holds even though the definition uses the first argument's head. Mathlib PiNat supplies firstDiff, its minimum inequality and the standard product metric.

**Theorem 1.1 (The strong triangle inequality).**

$$\begin{aligned}\forall w: HeadWeights,\\\forall x: \mathbb{N} \to \mathbb{N},\\\forall y: \mathbb{N} \to \mathbb{N},\\\forall z: \mathbb{N} \to \mathbb{N},\\\operatorname{distance}(w, x, z) \le \operatorname{max}(\operatorname{distance}(w, x, y), \operatorname{distance}(w, y, z))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.distance_ultra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal points are handled separately. With a common head, the first difference of x,z is at least the minimum of those on x,y and y,z; antitonicity gives the maximum bound. With mixed heads one comparison edge is one, while every distance is at most one. Positive weights separate distinct points and give the actual rawMetric MetricSpace.

**Theorem 1.2 (Uniform equivalence over every symbol).**

$$\begin{aligned}\forall w: HeadWeights,\\\forall b: \operatorname{UniformBounds}(w),\\\operatorname{uniformSpace}(\operatorname{rawMetric}(w)) = \operatorname{uniformSpace}(metricSpaceNatNat)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.uniformSpace_eq_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

UniformBounds has a positive lower(n) valid for every head and an upper(n) valid for every head, with arbitrarily small upper tails. Distance<lower(N) forces agreement through coordinate N. A prefix of length N gives distance<=upper(N). These two controls prove both uniform identity maps against PiNat.metricSpaceNatNat on all of N^N. Replacing the raw uniformity by this proved equality gives a metric with the actual discrete product uniformity and topology.

**Theorem 1.3 (Ordinary shadowing for uniform head weights).**

$$\begin{aligned}\forall w: HeadWeights,\\\forall b: \operatorname{UniformBounds}(w),\\\operatorname{MetricHasShadowing}(\operatorname{metric}(b), \operatorname{shift}(1))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.metric_hasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For epsilon>0 choose upper(N)<epsilon and delta=lower(N)>0. Each strict error forces overlap through N. The diagonal splice agrees through N+1 at every natural time, and the uniform tail bound gives strict epsilon tracing. There is no finite horizon or restriction of the carrier to a compact subset.

**Theorem 1.4 (The exact size of the only nonzero error).**

$$\begin{aligned}\forall w: HeadWeights,\\\forall p: \mathbb{N},\\\forall q: \mathbb{N},\\\forall N: \mathbb{N},\\p \neq q \Rightarrow\\\operatorname{distance}(w, \operatorname{shift}(1, \operatorname{defectOrbit}(p, q, N, 0)), \operatorname{defectOrbit}(p, q, N, 1)) = \operatorname{weight}(w, q, N-1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.defect_initial_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The time-zero sequence has p at coordinate zero and q elsewhere. The time-one sequence has p only at N-1. Every later sequence is the exact shift of its predecessor. The initial error has background head q and first difference N-1, hence exactly w(q,N-1); all later errors are zero.

**Theorem 1.5 (No full tracer below the preferred-head weight).**

$$\begin{aligned}\forall w: HeadWeights,\\\forall p: \mathbb{N},\\\forall q: \mathbb{N},\\\forall N: \mathbb{N},\\p \neq q \Rightarrow\\2 \le N \Rightarrow\\\forall r: \mathbb{R},\\r \le \operatorname{weight}(w, p, N) \Rightarrow\\\forall y: \mathbb{N} \to \mathbb{N},\\\neg \operatorname{MetricTraces}(\operatorname{rawMetric}(w), \operatorname{shift}(1), r, \operatorname{defectOrbit}(p, q, N), y)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.defect_no_tracer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Time zero first forces the tracer head to p, since a head mismatch has distance one. Antitonicity and the strict tracing bound then force y(N)=q. At time N the observed head is p and the tracer head is q, giving distance exactly one. Since r<=w(p,N)<=1, the strict tracing inequality is impossible.

**Theorem 1.6 (The standard diagonal has a half-error bound).**

$$\begin{aligned}\forall d: \mathbb{R},\\0 < d \Rightarrow\\\forall z: \mathbb{N} \to \mathbb{N} \to \mathbb{N},\\\operatorname{MetricPseudoOrbit}(metricSpaceNatNat, \operatorname{shift}(1), d, z) \Rightarrow\\\operatorname{MetricTraces}(metricSpaceNatNat, \operatorname{shift}(1), \frac{d}{2}, z, \operatorname{diagonalSplice}(z))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.standard_product_diagonal_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A first tracing mismatch j telescopes to an edge mismatch k<j. That edge's first difference m is at most k, so 2*(1/2)^j<=(1/2)^m<delta. Zero tracing errors are also strictly below delta/2. The same diagonal therefore supplies Lipschitz shadowing with L=1 for the entire standard product shift.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.defect_initial_error`
- Truth anchor: `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.defect_no_tracer`
- Truth anchor: `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.distance_ultra`
- Truth anchor: `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.metric_hasShadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.standard_product_diagonal_traces`
- Truth anchor: `D5/S1/Dynamics/Shadowing/HeadWeightedMetric.uniformSpace_eq_product`
- Dependency: [D5/S1/Dynamics/Shadowing/MetricTracing](MetricTracing.md)
