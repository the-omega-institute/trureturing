# Finite Prefix Local Constancy

## Abstract

A finite symbolic prefix is locally constant off its boundary union.

**Theorem 1.1 (A finite prefix has one common stability radius).**

$$\operatorname{LocallyConstantOff}(w, B) \land \theta \in \operatorname{outsidePrefixBoundary}(B, N) \Rightarrow \exists \varepsilon > 0,\ \forall \theta',\ d(\theta', \theta) < \varepsilon \Rightarrow \forall n, n < N,\ w_{n}(\theta') = w_{n}(\theta).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/SymbolicStability/FinitePrefixLocalConstancy.finite_prefix_locally_constant_off_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the nth symbol map be locally constant away from its nth boundary. If a point avoids the union of the first N boundaries, then one positive metric radius makes all N symbols constant at once.

Pinned Mathlib has no complete theorem matching this common-radius statement. The Lean proof applies Filter.eventually_all to combine the finite family of neighborhood properties, then applies Metric.eventually_nhds_iff to extract the positive radius. The related LocallyConstant.unflip construction assumes global local constancy and is therefore stronger than the pointwise input here.

## References

- Truth anchor: `D5/S3/Observer/SymbolicStability/FinitePrefixLocalConstancy.finite_prefix_locally_constant_off_boundary`
