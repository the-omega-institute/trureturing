# Orbit-Variance RH Criterion

## Abstract

Vanishing finite-height completion variance characterizes the abstract critical-line condition under explicit coverage and positive-multiplicity premises.

**Theorem 1.1 (Zero orbit variance is equivalent to the critical-line condition).**

$$\forall \xi: \mathbb{C} \to \mathbb{C}, \mu: \mathbb{C} \to \mathbb{N}, W,\ (\forall \rho, \xi(\rho)=0 \land 0<\operatorname{Im}(\rho) \Rightarrow 0<\mu(\rho)) \Rightarrow\ (\forall \rho, \xi(\rho)=0 \Rightarrow \exists \Sigma, \xi(\Sigma)=0 \land 0<\operatorname{Im}(\Sigma) \land \operatorname{Re}(\Sigma)=\operatorname{Re}(\rho)) \Rightarrow\ (\operatorname{CLH}(\xi) \Leftrightarrow \forall T, 0<T \Rightarrow \operatorname{completionVariance}(W(T), \mu)=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/OrbitVarianceRiemannCriterion.orbit_variance_rh_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive height, a finite zero window records exactly the positive-ordinate zeros below that height. Multiplicities are required to be positive at those zeros, so every off-line zero in a window contributes a strictly positive summand.

Mathlib's nonnegative finite-sum criterion gives that the variance vanishes exactly when every multiplicity-weighted squared critical displacement vanishes. Choosing T=Im(rho)+1 detects each positive-ordinate off-line zero.

Because the imported window definition only contains zeros with positive ordinate, the all-zero statement explicitly assumes that every zero's real part has a positive-ordinate representative. The assumption is visible rather than hidden inside the critical-line predicate.

Two concrete checks exclude vacuity: the imported xi(rho)=rho-i witness has variance 1/4 at height two, while a singleton zero at 1/2+i lies on the critical line and has variance zero.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/OrbitVarianceRiemannCriterion.orbit_variance_rh_criterion`
- Dependency: [D5/S3/Weil/ZetaLinear/FiniteHeightCompletionVariance](FiniteHeightCompletionVariance.md)
