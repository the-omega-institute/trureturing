# Coordinate Separation

## Abstract

Joint linear coordinates separate points exactly when their common kernels are trivial.

**Theorem 1.1 (Joint coordinates separate exactly at trivial common kernel).**

$$\forall R, M, I, N,\ q: \prod_{i} (M \to N_{i}),\ \operatorname{Injective}\left(pi(q)\right) \iff (\operatorname{iInf}_{i \in I} \ker_{Setoid}(q_{i}) = \Delta_{M}) \land (\operatorname{iInf}_{i \in I} \ker_{Linear}(q_{i}) = \{0\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/CoordinateSeparation.coordinate_separation_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be an indexed family of linear maps from one module M into modules N_i. Its joint coordinate map sends a point to all q_i values.

The joint map is injective exactly when the infimum of its component Setoid kernels is the diagonal relation and the infimum of its component linear kernels is the zero submodule.

This closes theorem/30.6 from qdo-v1 in its linear form. The bottom Setoid is literal equality, so the first condition is the source criterion that the limiting indistinguishability relation is the diagonal; the second is its linear common-kernel equivalent.

Pinned Mathlib supplied Setoid.injective_iff_ker_bot, LinearMap.ker_pi, and LinearMap.ker_eq_bot_of_injective, all applied by the Lean proof. Loogle returned the first two identities; local source search found the linear helper. D5 search found no equivalent separation theorem. LeanSearch's API returned HTTP 404 and supplied no conclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/CoordinateSeparation.coordinate_separation_criterion`
