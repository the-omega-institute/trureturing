# Compact Local Realization

## Abstract

Finite local realizability of closed records on a compact carrier yields one global realization.

**Theorem 1.1 (Finite local compatibility implies global compatibility).**

$$\begin{gathered}\forall X, C, B: \operatorname{Type},\\{}[\operatorname{TopologicalSpace}(X)], [\operatorname{CompactSpace}(X)],\\{}beta: C \to X \to B, b: C \to B,\\{}\forall C: C, \operatorname{IsClosed}(\operatorname{setOf}(beta(C) x = b(C))), \forall s: \operatorname{Finset}(C), \exists x, \forall C: C, C \in s \Rightarrow beta(C, x) = b(C) \Rightarrow\\{}\exists x, \forall C: C, beta(C) x = b(C).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/CompactLocalRealization.compact_local_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each context, the equality fiber of the continuous local record is closed. Every finite family of fibers is nonempty, so compactness gives a point in their total intersection.

## References

- Truth anchor: `D5/S3/Observer/Completion/CompactLocalRealization.compact_local_realization`
