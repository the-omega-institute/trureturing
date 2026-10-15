# Metric Tracing and Infinite Diagonal Splices

## Abstract

Strict infinite metric tracing agrees with uniform tracing without compactness; symbolic overlaps propagate along a diagonal.

A metric pseudo-orbit z satisfies dist(f(z(i)),z(i+1))<delta at every natural i. MetricTraces(f,epsilon,z,y) means dist(f^i(y),z(i))<epsilon for all i, including zero. MetricHasShadowing chooses a positive delta for each positive epsilon before the sequence. HasLipschitzShadowing chooses positive L and cutoff before every positive delta at most the cutoff, and traces with strict bound L delta.

**Theorem 1.1 (The noncompact metric entourage bridge).**

$$\begin{aligned}\forall X: Type,\\{}[\operatorname{PseudoMetricSpace}(X)],\\\forall f: X \to X,\\\operatorname{MetricHasShadowing}(f) \iff \operatorname{UniformHasShadowing}(f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MetricTracing.metric_shadowing_iff_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entourage contains a strict distance ball around the diagonal. Apply metric shadowing to its radius and use a strict control ball as the uniform entourage. Conversely, apply uniform shadowing to the prescribed strict metric entourage and choose a control radius inside the returned entourage. This uses Metric.mem_uniformity_dist and Metric.dist_mem_uniformity, without finite covers, local compactness, compactness or surjectivity.

**Theorem 1.2 (Quantitative tracing implies ordinary tracing).**

$$\begin{aligned}\forall X: Type,\\{}[\operatorname{PseudoMetricSpace}(X)],\\\forall f: X \to X,\\\operatorname{HasLipschitzShadowing}(f) \Rightarrow\\\operatorname{MetricHasShadowing}(f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MetricTracing.metricHasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For accuracy epsilon use delta=min(cutoff,epsilon/(2L)). Positivity and L delta at most epsilon/2 preserve strict tracing.

**Theorem 1.3 (Natural iterates of the existing shift).**

$$\begin{aligned}\forall A: Type,\\\forall x: \mathbb{N} \to A,\\\forall i: \mathbb{N},\\\forall j: \mathbb{N},\\\operatorname{iterate}(\operatorname{shift}(1), i, x, j) = \operatorname{apply}(x, i+j)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MetricTracing.shift_one_iterate_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SymbolicDynamics.FullShift.shift(1) sends x(j) to x(j+1); its i-th iterate reads x(i+j).

**Theorem 1.4 (An extra coordinate from diagonal overlap).**

$$\begin{aligned}\forall A: Type,\\\forall z: \mathbb{N} \to \mathbb{N} \to A,\\\forall N: \mathbb{N},\\(\forall i: \mathbb{N},\forall j: \mathbb{N},j \le N \Rightarrow \operatorname{apply}(z, i, j+1) = \operatorname{apply}(z, i+1, j)) \Rightarrow\\\forall i: \mathbb{N},\\\forall j: \mathbb{N},\\j \le N+1 \Rightarrow\\\operatorname{apply}(\operatorname{diagonalSplice}(z), i+j) = \operatorname{apply}(z, i, j)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MetricTracing.diagonal_splice_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The splice is y(k)=z(k)(0), an element of the full product. Induction on j transports z(i+j)(0) backwards along overlap identities. Every edge agrees through N, so each shifted splice agrees through N+1 with z(i), simultaneously for every natural time.

**Theorem 1.5 (A mismatch must cross an earlier edge).**

$$\begin{aligned}\forall A: Type,\\\forall z: \mathbb{N} \to \mathbb{N} \to A,\\\forall i: \mathbb{N},\\\forall j: \mathbb{N},\\\operatorname{apply}(\operatorname{diagonalSplice}(z), i+j) \neq \operatorname{apply}(z, i, j) \Rightarrow\\\exists t, \exists k,i \le t \land t < i+j \land k < j \land \operatorname{apply}(z, t, k+1) \neq \operatorname{apply}(z, t+1, k)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MetricTracing.diagonal_mismatch_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mismatch at coordinate j of time i either occurs on the current edge at j-1 or survives at time i+1 with coordinate j-1. Iteration terminates before time i+j, since diagonal coordinates at j=0 agree by definition. Thus i<=t<i+j and k<j for an actual mismatching edge.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/MetricTracing.diagonal_mismatch_edge`
- Truth anchor: `D5/S1/Dynamics/Shadowing/MetricTracing.diagonal_splice_overlap`
- Truth anchor: `D5/S1/Dynamics/Shadowing/MetricTracing.metricHasShadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/MetricTracing.metric_shadowing_iff_uniform`
- Truth anchor: `D5/S1/Dynamics/Shadowing/MetricTracing.shift_one_iterate_apply`
- Dependency: [D5/S1/Dynamics/Shadowing/UniformTracing](UniformTracing.md)
