# Real Unit-Interval Zeta Nonvanishing

## Abstract

Riemann zeta is nonzero at every real point strictly between zero and one.

**Theorem 1.1 (Riemann zeta is nonzero on the open real unit interval).**

$$\forall sigma\in \mathbb{R},\ 0<sigma \land sigma<1 \Rightarrow \zeta(sigma) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/RealUnitIntervalZetaNonvanishing.riemannZeta_ne_zero_on_real_unit_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof pairs adjacent terms of the alternating Dirichlet series. Uniform convergence on compact subsets of the positive half-plane makes the paired series analytic, and the identity principle identifies it with the eta factor times Riemann zeta.

At a positive real argument every adjacent pair is strictly positive. The eta factor therefore cannot vanish; for an argument below one, this forces the zeta value to be nonzero. Pinned Mathlib provides the series and analytic ingredients but no theorem with this open real-interval conclusion.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/RealUnitIntervalZetaNonvanishing.riemannZeta_ne_zero_on_real_unit_interval`
