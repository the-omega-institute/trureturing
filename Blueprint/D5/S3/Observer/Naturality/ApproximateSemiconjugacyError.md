# Approximate Semiconjugacy Error

## Abstract

A uniform semiconjugacy defect controls finite-time orbit error by geometric sums.

**Theorem 1.1 (Approximate semiconjugacy error).**

$$\begin{gathered}\forall Y, Z: Type,\\[\operatorname{PseudoMetricSpace} Z],\\\forall \tau: Y\to Y, \sigma: Z\to Z, \pi: Y\to Z,\\\forall L, \Delta: \operatorname{NNReal},\\(\operatorname{LipschitzWith}(L, \sigma) \land \forall y \in Y, d_{Z}(\pi(\tau(y)), \sigma(\pi(y))) \leq \Delta) \Rightarrow\\(\forall k \in \mathbb{N}, \forall y \in Y,\ d_{Z}(\pi(\tau^{k}(y)), \sigma^{k}(\pi(y))) \leq \Delta \sum_{j=0}^{k-1} L^j) \land \\(L < 1 \Rightarrow \forall k \in \mathbb{N}, \forall y \in Y,\ d_{Z}(\pi(\tau^{k}(y)), \sigma^{k}(\pi(y))) \leq \frac{\Delta}{1-L}) \land \\(L = 1 \Rightarrow \forall k \in \mathbb{N}, \forall y \in Y,\ d_{Z}(\pi(\tau^{k}(y)), \sigma^{k}(\pi(y))) \leq k \Delta).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/ApproximateSemiconjugacyError.approximate_semiconjugacy_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau update the concrete state space Y, let sigma update the pseudometric space Z, and let pi project concrete states into Z. The nonnegative number L is a Lipschitz constant for sigma, and every one-step semiconjugacy defect is at most delta.

For every natural k and state y, the orbit discrepancy is bounded by delta times the finite geometric sum through exponent k minus one. When k is zero, the range and its sum are empty.

The same declaration also states both requested specializations. If L is less than one, the error is bounded by delta divided by one minus L. If L equals one, it is bounded by k times delta.

The proof applies the frozen uniform output-trajectory theorem with identity readout and zero readout error. Mathlib's nonnegative-real geometric-series sum and the finite sum at L equal to one give the two corollaries.

## References

- Truth anchor: `D5/S3/Observer/Naturality/ApproximateSemiconjugacyError.approximate_semiconjugacy_error`
- Dependency: [D5/S3/Observer/MetricGeometry/OutputTrajectoryError](../MetricGeometry/OutputTrajectoryError.md)
