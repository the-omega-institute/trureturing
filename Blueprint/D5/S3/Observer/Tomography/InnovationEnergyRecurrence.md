# Innovation-Energy Recurrence

## Abstract

Nested observation spaces split residual energy into later residual and innovation.

**Theorem 1.1 (Nested observation spaces split residual energy).**

$$\forall U, W\in \operatorname{Sub}(V),\ U \subseteq W \Rightarrow \forall x\in V,\ \operatorname{residualEnergy}(U, x) = \operatorname{residualEnergy}(W, x) + \Vert\operatorname{proj}_{\operatorname{innovationSubspace}(U, W)}(x)\Vert^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/InnovationEnergyRecurrence.innovation_energy_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be contained in W in a finite-dimensional real inner-product space. The residual energy of x at a subspace is the squared norm of its orthogonal projection onto the subspace complement. The innovation subspace is the intersection of U's orthogonal complement with W.

Project the U-residual onto the innovation subspace and its orthogonal complement. Nestedness identifies the first component with the innovation projection of x. Projection uniqueness identifies the second component with the W-residual, because their difference lies in the innovation subspace.

Loogle found the exact pinned-Mathlib squared-norm decomposition Submodule.norm_sq_eq_add_norm_sq_starProjection, which is imported and applied. A second Loogle query required a namespace correction; LeanSearch API attempts returned only HTTP capability failures. Repository and formalization searches found no existing innovation-energy recurrence.

The result is finite-dimensional and real. It formalizes the exact one-step energy identity for nested observation spaces; it does not add time-indexed observer dynamics or an infinite-dimensional closed-subspace extension.

## References

- Truth anchor: `D5/S3/Observer/Tomography/InnovationEnergyRecurrence.innovation_energy_recurrence`
