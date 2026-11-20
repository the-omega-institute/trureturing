# Normal subgroup fixed seed mass

## Abstract

Maximum fixed seed mass for a normal subgroup of the acting group.

**Theorem 1.1 (The least row bound is attained under the full group action).**

$$\forall H, P, \operatorname{Normal}\left(H\right) \land \operatorname{CovariantProbabilityKernel}\left(P\right) \Rightarrow \exists x, (\forall y, \operatorname{RowFixedMass}\left(H, P, x\right) \le \operatorname{RowFixedMass}\left(H, P, y\right)) \land \operatorname{UniversalFixedMassBound}\left(H, P, \operatorname{RowFixedMass}\left(H, P, x\right)\right) \land \operatorname{PositiveInvariantAttainment}\left(H, P, \operatorname{RowFixedMass}\left(H, P, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass.maximal_normal_subgroup_fixed_seed_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts on a nonempty finite input set X and a finite output set Y. Let H be a normal subgroup of G. The probability kernel P is covariant under G. The H row mass sums P over outputs fixed by all elements of H that fix that input.

The same minimizing row bounds the total weight of H-fixed seeds of every finite calibration with nonnegative weights and a G-covariant readout. There is an attaining finite calibration with positive weights summing to one, invariant under G, with all marginals equal to P.

Apply the full-group fixed mass theorem to H. Send each seed to its deterministic table. The table law has the required marginals, and every H-fixed seed maps to an H-fixed table. Average this law over the finite image of G acting on the table space. Covariance preserves the marginals in each translated law. Normality ensures that each translate preserves the set of H-fixed tables. Restrict to the positive support of the averaged law and use the row bound to obtain equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass.maximal_normal_subgroup_fixed_seed_mass`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FixedKernelMass](FixedKernelMass.md)
