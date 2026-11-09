# Pointwise North-South Stability and Compact Uniformity

## Abstract

Two-sided pointwise north-south dynamics forces stable poles and uniform attraction on compact sets away from the opposite pole.

**Theorem 1.1 (Stability and uniform attraction are conclusions).**

$$\forall M: CompactMetricSpace, \forall f: \operatorname{Homeomorphism}(M), \forall N: M, \forall S: M, \operatorname{Pointwise}(f, N, S) \Rightarrow \operatorname{Stable}(f, S) \land \operatorname{Stable}(\operatorname{inverse}(f), N) \land (\forall C: \operatorname{Set}(M), (\operatorname{IsCompact}(C) \land \neg (N \in C)) \Rightarrow \forall O: \operatorname{Neighborhoods}(S), \exists T: \mathbb{N}, \forall n: \mathbb{N}, T \le n \Rightarrow \operatorname{image}(\operatorname{power}(f, n), C) \subseteq O) \land (\forall C: \operatorname{Set}(M), (\operatorname{IsCompact}(C) \land \neg (S \in C)) \Rightarrow \forall O: \operatorname{Neighborhoods}(N), \exists T: \mathbb{N}, \forall n: \mathbb{N}, T \le n \Rightarrow \operatorname{image}(\operatorname{power}(\operatorname{inverse}(f), n), C) \subseteq O)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/PointwiseNorthSouth.stability_and_compact_uniformity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M is an arbitrary compact metric space and f is a homeomorphism. The distinct poles N and S are fixed. Every other point converges to S under nonnegative powers of f and to N under nonnegative powers of its inverse. These are pointwise assumptions; stability, uniformity, local connectedness, a flow and differentiability are not premises.

Both poles are Lyapunov stable in the appropriate direction. On every compact C excluding N, all sufficiently large forward iterates lie in any prescribed neighborhood of S, uniformly over C. The inverse assertion holds for compact C excluding S. Empty compact sets and the two-point space remain in scope.

Failure of stability gives first-exit points with exit times tending to infinity. A compact subsequential limit is outside a small pole neighborhood; every strictly negative iterate belongs to its closure, which excludes N. The pointwise backward limit gives the contradiction. Stable-entry neighborhoods then form a finite cover of each compact C, giving uniform attraction.

This is the first dependency of the supplied full north-south crossing-selector proof, public-proof.txt SHA-256 9d2c8af332171841b0de2122a8a6d18d3f094b8ee563ff2b50646332144306bc. It does not by itself construct the selector or settle Artigue's final Question 5.19, printed page 52 (arXiv v1 Question 5.21). The source is Alfonso Artigue, Shadowing maps, DOI 10.2140/om.2027.4.29. No priority or comprehensive literature novelty claim is made.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/PointwiseNorthSouth.stability_and_compact_uniformity`
