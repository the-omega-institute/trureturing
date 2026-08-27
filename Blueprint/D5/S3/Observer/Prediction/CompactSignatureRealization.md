# Compact Signature Realization

## Abstract

Finite compatibility of continuous protocol readouts on a compact state space has one global realization.

**Theorem 1.1 (Finite compatibility gives a global realizing state).**

$$\begin{gathered}\forall P, X: \operatorname{Type}, \Lambda: P \to \operatorname{Type},\\{}[\operatorname{TopologicalSpace}(X)], [\operatorname{CompactSpace}(X)],\\{}[\forall p: P, \operatorname{TopologicalSpace}(\Lambda(p))], [\forall p: P, \operatorname{T2Space}(\Lambda(p))],\\{}e: (p: P) \to \operatorname{ContinuousMap}(X, \Lambda(p)),\\{}\lambda: (p: P) \to \Lambda(p),\\{}(\forall F: \operatorname{Set}(P), \operatorname{Finite}(F) \Rightarrow \exists x: X, \forall p\in F, e(p)(x) = \lambda(p)) \Rightarrow\\{}\exists x: X, \forall p: P, e(p)(x) = \lambda(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Prediction/CompactSignatureRealization.finite_compatibility_global_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P is the protocol carrier, X is the compact state carrier, and Lambda assigns a Hausdorff output carrier to each protocol. Each protocol readout is continuous, and signature selects its prescribed value.

Finite compatibility says that every finite protocol set has a common realizing state. The corresponding coordinate fibers are closed, so compactness supplies a point in their full intersection.

## References

- Truth anchor: `D5/S3/Observer/Prediction/CompactSignatureRealization.finite_compatibility_global_realization`
