# Normal subgroup fixed seed mass

## Abstract

Maximum fixed seed mass for a normal subgroup of the acting group.

**Theorem 1.1 (The least row bound is attained under the full group action).**

$$\forall G, H, X, Y, P, \operatorname{NormalSubgroup}\left(H, G\right) \land \operatorname{NonemptyFiniteInput}\left(X, v\right) \land \operatorname{FiniteOutputWithDecidableEquality}\left(Y, w\right) \land \operatorname{CovariantProbabilityKernel}\left(G, X, Y, P\right) \Rightarrow \exists x, (\forall y, \operatorname{RowFixedMass}\left(H, P, x\right) \le \operatorname{RowFixedMass}\left(H, P, y\right)) \land \operatorname{UniversalFixedMassBound}\left(H, P, \operatorname{RowFixedMass}\left(H, P, x\right), s\right) \land \operatorname{PositiveInvariantAttainment}\left(H, P, \operatorname{RowFixedMass}\left(H, P, x\right), \operatorname{MaxUniverse}\left(v, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass.maximal_normal_subgroup_fixed_seed_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts on a nonempty finite input type X in universe v and a finite output type Y in universe w with decidable equality. Let H be a normal subgroup of G. The probability kernel P is covariant under G. The H row mass sums P over outputs fixed by all elements of H that fix that input.

The same minimizing row bounds the total weight of H-fixed seeds for every finite seed type in universe s, with s arbitrary, given nonnegative weights and a pointwise G-covariant deterministic readout with marginals P. An attaining finite seed type lives in the maximum of the input and output type universes. Its weights are positive, sum to one, and are G-invariant. Its deterministic readout is pointwise G-covariant and has marginals P.

Apply the full-group fixed mass theorem to H. Send each seed to its deterministic table. The table law has the required marginals, and every H-fixed seed maps to an H-fixed table. Average this law over the finite image of G acting on the table space. Covariance preserves the marginals in each translated law. Normality ensures that each translate preserves the set of H-fixed tables. Restrict to the positive support of the averaged law and use the row bound to obtain equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass.maximal_normal_subgroup_fixed_seed_mass`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FiniteTableCalibration](FiniteTableCalibration.md)
