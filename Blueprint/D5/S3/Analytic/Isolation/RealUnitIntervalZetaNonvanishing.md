# Positive Real-Axis Zeta Nonvanishing

## Abstract

Riemann zeta is nonzero at every positive real point other than one; the open unit interval follows.

**Theorem 1.1 (Riemann zeta is nonzero at positive real points away from one).**

$$\forall x\in \mathbb{R},\ 0<x \land x\neq1 \Rightarrow \zeta(x) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing.riemannZeta_ne_zero_of_real_pos_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof pairs adjacent terms of the alternating Dirichlet series. Uniform convergence on compact subsets of the positive half-plane makes the paired series analytic, and the identity principle identifies it with the eta factor times Riemann zeta.

At every positive real argument each adjacent pair is strictly positive. The paired eta series therefore cannot vanish, so its factorization forces the zeta value to be nonzero away from one. This theorem is the public owner of the real-axis family; its eta machinery remains local and introduces no additional named API.

**Theorem 1.2 (Riemann zeta is nonzero on the open real unit interval).**

$$\forall sigma\in \mathbb{R},\ 0<sigma \land sigma<1 \Rightarrow \zeta(sigma) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing.riemannZeta_ne_zero_on_real_unit_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the direct open-unit-interval corollary of the public positive real-axis theorem: an argument strictly below one is not one.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing.riemannZeta_ne_zero_of_real_pos_ne_one`
- Truth anchor: `D5/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing.riemannZeta_ne_zero_on_real_unit_interval`
