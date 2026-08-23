# Stable Depth Cardinality Bounds

## Abstract

Stable prediction depth is bounded by the available complete-future quotient classes.

**Theorem 1.1 (Stable depth bounds for finite runtimes and token carriers).**

$$\begin{gathered}\forall Y, O, [\operatorname{Fintype}(Y)], [\operatorname{Fintype}(O)], [\operatorname{Nonempty}(Y)],\\{}F: Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\{}(m_{*} \leq \lvert Y/\equiv_{\infty} \rvert - \lvert O \rvert \leq \lvert Y \rvert - \lvert O \rvert) \land \\{}(\forall \Sigma, L, [\operatorname{Fintype}(\Sigma)], [\operatorname{Nonempty}(\Sigma)],\\{}F: \Sigma^{L} \to \Sigma^{L}, r: \Sigma^{L} \to \Sigma, \operatorname{Surjective}(r) \Rightarrow m_{*}(F, r) \leq \lvert \Sigma \rvert^{L} - \lvert \Sigma \rvert).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Prediction/StableDepthCardinalityBounds.stable_depth_runtime_and_token_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a nonempty finite deterministic runtime, let F update its state, and let q map Y surjectively onto the actual output carrier O. The least stable depth is defined by equality of two consecutive finite-future readout relations, while the complete relation compares all future readout coordinates.

The stable finite relation equals the complete-future relation. Therefore the exact finite refinement bound identifies the terminal class count with the cardinality of Y modulo complete-future equality and the initial class count with the cardinality of O.

For a minimal length-L token model, the runtime carrier is the full function type from Fin L to the token alphabet Sigma and the surjective output carrier is Sigma itself. The finite function-cardinality formula then specializes the general bound to |Sigma|^L - |Sigma|.

The source's final bullets distinguish prediction-classification depth from degradation time, parameter count, cycle-entry time, and semantic memory. Those explanatory contrasts introduce no in-scope predicates and are not asserted as invented universal clauses.

## References

- Truth anchor: `D5/S3/Observer/Prediction/StableDepthCardinalityBounds.stable_depth_runtime_and_token_bounds`
- Dependency: [D5/S3/Observer/Separation/FiniteHistoryStability](../Separation/FiniteHistoryStability.md)
