# Finite Stability Class Bound

## Abstract

The least finite-future stability depth obeys the exact quotient-class bound.

**Theorem 1.1 (Least finite-future stability depth).**

$$\begin{gathered}\forall X, Q: \operatorname{Type}, [\operatorname{Fintype}(X)],\\{}F: X \to X, q: X \to Q,\\{}m_{*} = \operatorname{sInf} \{n\in\mathbb{N} \mid K_{n} = K_{n+1}\},\\{}K_{m_{*}} = K_{m_{*}+1} = K_{\infty} \land \\{}(\forall n, K_{n} = K_{n+1} \Rightarrow m_{*} \leq n) \land \\{}m_{*} \leq \lvert X/K_{\infty} \rvert - \lvert X/K_{q} \rvert \leq \lvert X \rvert - \lvert \operatorname{Im}(q) \rvert.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Prediction/FiniteStabilityClassBound.finite_stability_class_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite state carrier, let F be its deterministic update, and let q be an arbitrary readout. The relation K_n identifies states with equal readouts from time zero through time n, while K_infinity identifies states with equal readouts at every time.

The displayed depth is the canonical least index where two adjacent finite-future relations agree. At that depth both adjacent relations equal the complete-future relation, and the quantified clause states minimality directly.

Each strict refinement creates at least one new quotient class. The resulting depth is therefore bounded by the difference between the complete-future and current-readout quotients; the canonical kernel-quotient equivalence identifies the latter with the realized image of q.

## References

- Truth anchor: `D5/S3/Observer/Prediction/FiniteStabilityClassBound.finite_stability_class_bound`
- Dependency: [D5/S3/Observer/Prediction/StableDepthCardinalityBounds](StableDepthCardinalityBounds.md)
