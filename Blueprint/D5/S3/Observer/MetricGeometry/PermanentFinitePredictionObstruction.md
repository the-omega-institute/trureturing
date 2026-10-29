# Permanent finite-prediction obstruction

## Abstract

A finite autonomous predictor cannot maintain a fixed subunit error forever on an irrational circle rotation.

**Theorem 1.1 (No permanent finite prediction).** Let `S` be a finite state type, `G : S → S` an autonomous update, `h : S → ℂ` a readout, and `initial : S`. For `x : AddCircle 1` and real `α` and `ε`, assume `α` is irrational, `0 < ε < 1/2`, and

$$
\forall n \in \mathbb N,\quad
\left\|h(G^n(\mathrm{initial}))-
\bigl(x+n\alpha\bigr).\mathrm{toCircle}\right\|\leq \varepsilon.
$$

Then `False`.

*Proof.* Machine-checked in Lean as `D5.S3.Observer.MetricGeometry.PermanentFinitePredictionObstruction.no_permanent_finite_prediction`. The proof applies the finite-horizon arithmetic obstruction at a natural horizon strictly larger than its fixed bound. ∎

*Source.* Repository-derived.

*Commentary.* The result is an infinite-horizon consequence of the existing finite-predictor horizon bound. It concerns finite autonomous state and a fixed subunit error threshold; it does not assert a rate for approximate predictors with a changing horizon or for non-autonomous systems.

## References

- Truth anchor: `D5.S3.Observer.MetricGeometry.PermanentFinitePredictionObstruction.no_permanent_finite_prediction`
- Dependency: `D5.S3.Observer.MetricGeometry.ArithmeticHorizon`
