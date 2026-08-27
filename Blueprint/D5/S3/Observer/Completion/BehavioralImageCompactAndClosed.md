# Behavioral Image Compactness and Closedness

## Abstract

A continuous behavior map from a compact state space into a Hausdorff dependent product has compact and closed range.

**Theorem 1.1 (The behavioral image is compact and closed).**

$$\begin{gathered}\forall P, X: \operatorname{Type}, Lambda: P \to \operatorname{Type},\\{}[\operatorname{TopologicalSpace}\left(X\right)], [\operatorname{CompactSpace}\left(X\right)],\\{}\forall p: P, [\operatorname{TopologicalSpace}\left(Lambda\left(p\right)\right)],\\{}\forall p: P, [\operatorname{T2Space}\left(Lambda\left(p\right)\right)],\\{}q: (\forall p: P, X \to Lambda\left(p\right)),\\{}\forall p: P, \operatorname{Continuous}\left(q\left(p\right)\right) \Rightarrow\\{}\operatorname{IsCompact}\left(\operatorname{range}\left(x \mapsto (p \mapsto q\left(p\right)\left(x\right))\right)\right) \land\\{}\operatorname{IsClosed}\left(\operatorname{range}\left(x \mapsto (p \mapsto q\left(p\right)\left(x\right))\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/BehavioralImageCompactAndClosed.behavioral_image_compact_and_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed behavior map sends a state x to the dependent tuple of all coordinate readouts q_p(x). Coordinatewise continuity gives continuity into the product topology.

The range of a continuous map from a compact space is compact. Every coordinate is Hausdorff, hence so is the dependent product, and a compact subset of that product is closed.

## References

- Truth anchor: `D5/S3/Observer/Completion/BehavioralImageCompactAndClosed.behavioral_image_compact_and_closed`
