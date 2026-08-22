# One-Step Hedging Gain

## Abstract

A nonzero orthogonal innovation gives the exact one-step squared hedging gain.

**Theorem 1.1 (A nonzero innovation gives the exact squared hedging gain).**

$$\forall V: \operatorname{FiniteDimensionalRealInnerProductSpace},\ \forall M, Mnext\in \operatorname{Submodule}(V),\ \forall x, residual\in V,\ M \subseteq Mnext \land \operatorname{innovationSubspace}(M, Mnext) = \operatorname{span}(residual) \land residual \neq 0 \Rightarrow \operatorname{dist}(x, M)^{2} - \operatorname{dist}(x, Mnext)^{2} = \frac{\lvert \langle x, residual \rangle \rvert^{2}}{\Vert residual \Vert^{2}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/OneStepHedgingGain.one_step_hedging_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be contained in Mnext in a finite-dimensional real inner-product space. Assume the directions added to M are exactly the line spanned by a nonzero residual vector.

For every target x, the decrease in squared metric distance to the attainable subspace is the squared absolute inner product with the residual, divided by the residual's squared norm.

The proof imports the repository's innovation_energy_recurrence. Pinned Mathlib exact-name searches and Loogle each found Submodule.starProjection_singleton and Submodule.starProjection_minimal; Metric.infDist_eq_iInf connects the minimizing projection to distance. Two initial natural-language smart-search queries exited after their declaration-name scan and are not counted as negative search results.

This closes qdo-v1 theorem/34.5, atom qdo-residual-97fbc85483c01bc3d120362dee0903ecffe71aeb5b4dc5668678e8fa439f0eb0. The statement covers the displayed one-step gain identity; it does not assert any additional market-completeness conclusion.

## References

- Truth anchor: `D5/S3/ResourceOrder/OneStepHedgingGain.one_step_hedging_gain`
- Dependency: [D5/S3/Observer/Tomography/InnovationEnergyRecurrence](../Observer/Tomography/InnovationEnergyRecurrence.md)
