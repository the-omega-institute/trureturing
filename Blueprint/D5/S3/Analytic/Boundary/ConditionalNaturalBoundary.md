# Conditional Natural Boundary and Gate

## Abstract

Accumulating genuine poles force the conditional imaginary-axis boundary, while any analytic gate exposes one of two rigid cancellation channels.

**Theorem 1.1 (Accumulating poles force the boundary and classify a gate).**

$$\begin{aligned}\forall f: \mathbb{C} \to \mathbb{C},\\{}\forall scale: \mathbb{N} \to \mathbb{R}, height: \mathbb{R} \to \mathbb{N} \to \mathbb{R},\\{}\forall tailNonvanishing, lineCondition, alternateCondition: \operatorname{Prop},\\{}\forall scaledZeroPattern, tailZeroCollision: \mathbb{R} \to \mathbb{N} \to \operatorname{Prop},\\{}\forall hscale: \operatorname{Tendsto}(scale, \operatorname{atTop}, \operatorname{atTop}),\\{}\forall hheight: (\forall target: \mathbb{R}, \operatorname{Tendsto}((n: \mathbb{N} \mapsto \operatorname{height}(target, n) / \operatorname{scale}(n)), \operatorname{atTop}, \operatorname{nhds}(target))),\\{}\forall hpoles: (tailNonvanishing \land (lineCondition \lor alternateCondition) \Rightarrow \forall target: \mathbb{R}, \forall n: \mathbb{N}, \operatorname{meromorphicOrderAt}(f, \operatorname{candidatePoint}(scale, \operatorname{height}(target), n)) < 0),\\{}\forall hchannels: (\forall target: \mathbb{R}, \forall n: \mathbb{N}, \neg(\operatorname{meromorphicOrderAt}(f, \operatorname{candidatePoint}(scale, \operatorname{height}(target), n)) < 0) \Rightarrow \operatorname{scaledZeroPattern}(target, n) \lor \operatorname{tailZeroCollision}(target, n)),\\{}(tailNonvanishing \land (lineCondition \lor alternateCondition) \Rightarrow \forall target: \mathbb{R}, \neg\operatorname{AnalyticAt}(\mathbb{C}, f, (target: \mathbb{C}) \times I)) \land\\{}\forall target: \mathbb{R}, \operatorname{AnalyticAt}(\mathbb{C}, f, (target: \mathbb{C}) \times I) \Rightarrow \operatorname{Eventually}_{n \in \operatorname{atTop}} (\operatorname{scaledZeroPattern}(target, n) \lor \operatorname{tailZeroCollision}(target, n)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/ConditionalNaturalBoundary.conditional_natural_boundary_and_gate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real target t, the transported candidates 1/(2c_n) + i gamma_n(t)/c_n converge to it on the imaginary axis. Under tail nonvanishing and either zero-location condition, every candidate has negative meromorphic order and is therefore a genuine pole. Analyticity at it would hold throughout a neighborhood and hence eventually at the convergent candidates, contradicting their negative orders.

The same neighborhood argument gives the unconditional gate theorem. If the function is analytic at an axis target, all sufficiently late transported candidates are analytic and thus cannot have negative order. The supplied cancellation classification then puts each of them in either the scaled-zero pattern or the tail-zero collision channel.

Repository search found the exact candidate-accumulation theorem but no declaration combining it with both conclusions. The proof imports that limit directly and uses Mathlib's eventually_analyticAt and meromorphicOrderAt_nonneg. The analytic and number-theoretic inputs that make candidates into poles or classify their cancellation remain explicit hypotheses; this theorem closes their topological assembly.

This is the complete two-part formalization of source theorem 6.62: the conditional boundary statement and its unconditional contrapositive gate statement are retained in one conjunction.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/ConditionalNaturalBoundary.conditional_natural_boundary_and_gate`
- Dependency: [D5/S3/Analytic/ScaledPoleAccumulation](../ScaledPoleAccumulation.md)
