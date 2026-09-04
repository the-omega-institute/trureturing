# Completed Scalar Odd Coupling

## Abstract

A reflection-invariant analytic scalar has no linear or odd homogeneous response.

**Theorem 1.1 (A completed scalar has no linear odd coupling).**

$$\begin{gathered}\forall E: Type,\\{}\operatorname{NormedAddCommGroup}(E) \land \operatorname{NormedSpace}(\mathbb{R}, E) \Rightarrow\\{}\forall completedScalar: E \to \mathbb{R}, series: \operatorname{FormalMultilinearSeries}(\mathbb{R}, E, \mathbb{R}),\\{}\operatorname{HasFPowerSeriesAt}(completedScalar, series, 0) \land (\forall u: E, completedScalar\left(u\right) = completedScalar\left(-u\right)) \Rightarrow\\{}\operatorname{fderiv}(\mathbb{R}, completedScalar, 0) = 0 \land\\{}(\forall n: \mathbb{N}, \operatorname{Odd}(n) \Rightarrow \forall u: E, \left(series_{n}\right)\left({\lambda i: \operatorname{Fin}(n) \mapsto u}\right) = 0) \land\\{}(\forall n: \mathbb{N}, 0 < n \land (\exists u: E, \left(series_{n}\right)\left({\lambda i: \operatorname{Fin}(n) \mapsto u}\right) \neq 0) \Rightarrow \operatorname{Even}(n) \land 2 \leq n).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/CompletedScalarOddCoupling.completed_scalar_has_no_linear_odd_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a scalar readout on a real normed space admit a formal power series at zero and be invariant under reflection of its input.

Restricting the readout to every real line gives two equal one-variable power series, one in each orientation. Uniqueness then forces every odd diagonal coefficient to vanish.

The linear coefficient is the Frechet derivative. Consequently the derivative is zero, and every positive degree with a nonzero homogeneous diagonal term is even and at least two.

## References

- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/CompletedScalarOddCoupling.completed_scalar_has_no_linear_odd_coupling`
