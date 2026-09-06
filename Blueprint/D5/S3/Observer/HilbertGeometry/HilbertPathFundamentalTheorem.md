# Hilbert Path Fundamental Theorem

## Abstract

Actual derivatives and pointwise Bochner reconstruction for absolutely continuous Hilbert paths.

**Theorem 1.1 (Actual derivatives almost everywhere).**

$$\forall H: Type, [\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(Real, H\right)], [\operatorname{CompleteSpace}\left(H\right)],\\{}\forall f: Real \to H, \forall a, b: Real, \operatorname{AbsolutelyContinuousOnInterval}\left(f, a, b\right) \implies \operatorname{AlmostEverywhere}\left(volume, \lambda t: Real \mapsto t \in \operatorname{uIcc}\left(a, b\right) \implies \operatorname{HasDerivAt}\left(f, \operatorname{deriv}\left(f, t\right), t\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem.absolutely_continuous_interval_ae_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complete real Hilbert space H and every absolutely continuous path f, HasDerivAt holds with the totalized derivative at Lebesgue almost every point of the unordered closed interval. This implies actual differentiability; it is not inferred from totalization. No dimension or ambient separability hypothesis is imposed. Complex Hilbert spaces are included by restricting their scalar structure to the real numbers.

**Theorem 1.2 (Pointwise Bochner reconstruction).**

$$\forall H: Type, [\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(Real, H\right)], [\operatorname{CompleteSpace}\left(H\right)],\\{}\forall f: Real \to H, \forall a, b: Real, \operatorname{AbsolutelyContinuousOnInterval}\left(f, a, b\right) \implies \forall t: Real, t \in \operatorname{uIcc}\left(a, b\right) \implies \operatorname{intervalIntegral}\left(\operatorname{deriv}\left(f\right), a, t, volume\right) = \operatorname{f}\left(t\right) - \operatorname{f}\left(a\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem.absolutely_continuous_interval_integral_deriv_eq_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oriented Bochner interval integral with respect to Lebesgue measure reconstructs f at every point t of the interval, including its endpoints. The proof first passes to the separable closed span of the interval image. Scalar coordinate derivatives satisfy finite square-sum bounds controlled by signed variation. Their orthogonal series supplies a measurable, integrable Hilbert velocity. Coordinate integral exchange, scalar FTC and coordinate separation give pointwise reconstruction; differentiation of that Bochner primitive identifies the velocity with the actual derivative.

This is the analytic prerequisite for qdo-v1 theorem 36.26 and the named consumer absolutely_continuous_subspace_action_minimum_unique. The extended quadratic action, lower bound, affine attainment and pointwise uniqueness remain downstream. Absolute continuity alone does not imply finite quadratic energy. The private countable-basis helpers are a minimal Apache-2.0 source port from Kitware's immutable revision ef157afc71c3866cb608111ef61462516330ef56; their license and notice trail are retained in the Lean source.

## References

- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem.absolutely_continuous_interval_ae_hasDerivAt`
- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem.absolutely_continuous_interval_integral_deriv_eq_sub`
