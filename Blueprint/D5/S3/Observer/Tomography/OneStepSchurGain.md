# One-Step Schur Gain

## Abstract

A generated observation direction gives its exact normalized distance gain.

**Theorem 1.1 (A generated direction gives its normalized distance gain).**

$$\forall K: \operatorname{RCLike},\ \forall V: \operatorname{InnerProductSpace}(K),\ \forall S\in \operatorname{FiniteDimensionalSubmodule}(K, V),\ \forall target, generator\in V,\ residual = \operatorname{proj}_{S^{\perp}}(generator), next = \operatorname{sup}(S, \operatorname{span}(generator)),\ (residual \neq 0 \Rightarrow \operatorname{dist}(target, S)^{2} - \operatorname{dist}(target, next)^{2} = \frac{\lvert \langle target, residual \rangle \rvert^{2}}{\Vert residual \Vert^{2}}) \land\ (residual = 0 \Rightarrow \operatorname{dist}(target, next) = \operatorname{dist}(target, S)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/OneStepSchurGain.one_step_schur_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite-dimensional observation subspace of a real or complex inner-product space. Construct the residual of a new generator by projecting it onto the orthogonal complement of S, and construct the next observation space by adjoining the generator to S.

If the constructed residual is nonzero, the squared distance drop for any target is its squared coupling with the residual divided by the residual's squared norm. If the residual is zero, adjoining the generator does not change the target's distance.

Pinned Mathlib provides the exact projection identities Submodule.starProjection_singleton, Submodule.starProjection_minimal, Submodule.starProjection_orthogonal_val, and Submodule.norm_sq_eq_add_norm_sq_starProjection. The proof applies them on the source-constructed spaces. Repository searches found related nested-space and nonzero gain theorems, but no declaration with both generated-space cases.

This formalizes theorem 29.8. Both case clauses are public; the result does not assert convergence of a sequence of observation spaces.

## References

- Truth anchor: `D5/S3/Observer/Tomography/OneStepSchurGain.one_step_schur_gain`
