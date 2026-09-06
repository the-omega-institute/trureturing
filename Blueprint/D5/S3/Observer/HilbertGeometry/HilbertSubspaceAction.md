# Hilbert Subspace Action

## Abstract

Extended quadratic action on all absolutely continuous Hilbert paths with a closed-subspace initial constraint.

Let K be RCLike and H an arbitrary complete inner product space over K. Time, scalar multiplication along paths, and derivatives use the real scalar structure obtained by restriction of scalars. Thus real and complex Hilbert spaces are included, without separability or dimension assumptions. Let M be an actual closed linear subspace and x a target vector. Write P for its orthogonal starProjection, r = x - P x, and mu for Lebesgue measure restricted to Ioc(0,1). The half-open and closed interval integrals coincide because endpoints have measure zero. The notation S denotes quadraticAction, A denotes AdmissiblePath, and g denotes affinePath(M,x).

**Definition 1.1 (Extended action).**

$$\operatorname{S}\left(f\right) = \frac{1}{2} \operatorname{lintegral}\left(\lambda t: Real \mapsto \operatorname{ofReal}\left({\operatorname{norm}\left(\operatorname{deriv}\left(f, t\right)\right)}^{2}\right), mu\right)$$

*Formalization.* `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.quadraticAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every path f from Real to H, S(f) lies in ENNReal. The factor one-half and the integral are extended nonnegative real operations. Infinite quadratic action is permitted even when f is absolutely continuous.

**Definition 1.2 (Admissible paths).**

$$\operatorname{A}\left(M, x, f\right) \iff \operatorname{AbsolutelyContinuousOnInterval}\left(f, 0, 1\right) \land \operatorname{f}\left(0\right) \in M \land \operatorname{f}\left(1\right) = x$$

*Formalization.* `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.AdmissiblePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The path class requires only absolute continuity on the interval and the stated endpoints. It does not assume finite action, squared-derivative integrability, or any regularity outside the interval.

**Definition 1.3 (Affine path).**

$$\operatorname{g}\left(t\right) = \operatorname{P}\left(x\right) + \operatorname{smul}\left(t, r\right)$$

*Formalization.* `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.affinePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P is Mathlib's orthogonal projection onto M itself. This path is defined independently of the action and the minimizing property.

**Theorem 1.4 (Finite-action velocity defect).**

$$\forall K, H: Type, [\operatorname{RCLike}\left(K\right)], [\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(K, H\right)], [\operatorname{CompleteSpace}\left(H\right)],\\{}\forall f: Real \to H, \operatorname{AbsolutelyContinuousOnInterval}\left(f, 0, 1\right) \land \operatorname{S}\left(f\right) \neq \infty \implies\\{}\operatorname{MemLp}\left(\operatorname{deriv}\left(f\right), 2, mu\right) \land \operatorname{Integrable}\left(\lambda t: Real \mapsto {\operatorname{norm}\left(\operatorname{deriv}\left(f, t\right) - d\right)}^{2}, mu\right) \land \operatorname{AlmostEverywhere}\left(mu, \lambda t: Real \mapsto \operatorname{HasDerivAt}\left(f, \operatorname{deriv}\left(f, t\right), t\right)\right) \land\\{}\operatorname{integral}\left(\lambda t: Real \mapsto {\operatorname{norm}\left(\operatorname{deriv}\left(f, t\right)\right)}^{2}, mu\right) = {\operatorname{norm}\left(d\right)}^{2} + \operatorname{integral}\left(\lambda t: Real \mapsto {\operatorname{norm}\left(\operatorname{deriv}\left(f, t\right) - d\right)}^{2}, mu\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.finite_action_velocity_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here d = f(1) - f(0). The finite branch derives L2 membership of the totalized derivative and integrability of the squared velocity defect. The derivative is also proved to be the actual strong derivative almost everywhere. Endpoint reconstruction and the real inner-product norm expansion give the displayed exact variance identity.

**Theorem 1.5 (Affine attainment).**

$$\forall K, H: Type, [\operatorname{RCLike}\left(K\right)], [\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(K, H\right)], [\operatorname{CompleteSpace}\left(H\right)],\\{}\forall M: \operatorname{ClosedSubmodule}\left(K, H\right), \forall x: H,\\{}\operatorname{A}\left(M, x, g\right) \land \operatorname{S}\left(g\right) = \operatorname{ofReal}\left(\frac{{\operatorname{norm}\left(r\right)}^{2}}{2}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.affine_path_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine path is absolutely continuous, starts at P x in M, ends at x, and has constant derivative r and exactly the stated finite action.

**Theorem 1.6 (Minimum and pointwise uniqueness).**

$$\forall K, H: Type, [\operatorname{RCLike}\left(K\right)], [\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(K, H\right)], [\operatorname{CompleteSpace}\left(H\right)],\\{}\forall M: \operatorname{ClosedSubmodule}\left(K, H\right), \forall x: H,\\{}\operatorname{A}\left(M, x, g\right) \land \operatorname{S}\left(g\right) = \operatorname{ofReal}\left(\frac{{\operatorname{norm}\left(r\right)}^{2}}{2}\right) \land\\{}\forall f: Real \to H, \operatorname{A}\left(M, x, f\right) \implies (\operatorname{ofReal}\left(\frac{{\operatorname{norm}\left(r\right)}^{2}}{2}\right) \le \operatorname{S}\left(f\right) \land\\{}(\operatorname{S}\left(f\right) = \operatorname{ofReal}\left(\frac{{\operatorname{norm}\left(r\right)}^{2}}{2}\right) \iff \operatorname{EqOn}\left(f, g, \operatorname{Icc}\left(0, 1\right)\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.absolutely_continuous_subspace_action_minimum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the full minimum over all admissible AC paths. The infinite-action case satisfies the lower bound and cannot attain the finite minimum. For finite action, orthogonal Pythagoras and the velocity-defect identity force f(0) = P x and derivative r almost everywhere when equality holds. The frozen Hilbert path fundamental theorem then reconstructs f(t) = g(t) at every t in Icc(0,1), including both endpoints. Conversely, equality of the paths on that interval gives the same action. Values outside the interval play no role.

## References

- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.AdmissiblePath`
- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.absolutely_continuous_subspace_action_minimum_unique`
- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.affinePath`
- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.affine_path_attainment`
- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.finite_action_velocity_defect`
- Truth anchor: `D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.quadraticAction`
- Dependency: [D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem](HilbertPathFundamentalTheorem.md)
- Dependency: [D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability](VectorPathDerivativeIntegrability.md)
