# Infinite cost and self-gluing shortcuts

## Abstract

A two-point extended metric separates infinite paid cost from a zero-cost self-gluing shortcut.

Use Bool as a two-point extended metric space: equal points have distance zero and distinct points have distance infinity. The first datum has one piece, no generators and the identity family of points. Its chain rules therefore permit a one-step paid move from false to true, but that move has infinite cost.

The second datum has one closed singleton generator with domain {false}, range {true}, and the unique isometry between them. The forward gluing move changes false to true at zero cost. Both data have finite actual orbits, since the ambient tagged point type has only two elements. The statements below are the exact finite-chain consequences used at the boundary of the finite-cost hypothesis.

**Theorem 1.1 (The no-generator distance is infinite).**

$$distance\left(noGeneratorDatum, point\left(false\right), point\left(true\right)\right) = \infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InfiniteCostShortcutBoundary.no_generator_distance_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The infimum is infinity because every chain from false to true either stays at the same Bool value or has a paid move of cost infinity. An infinite-cost chain can still exist, so this statement concerns the distance value rather than nonexistence of a chain.

**Theorem 1.2 (An infinite-cost finite chain still exists).**

$$\exists t \in ENNReal,\; Chain\left(noGeneratorDatum, point\left(false\right), point\left(true\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InfiniteCostShortcutBoundary.no_generator_finite_chain_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness is the single paid move from false to true. Its cost is edist(false,true)=infinity, so the finite derivation has an extended cost of infinity.

**Theorem 1.3 (Self-gluing makes the distance zero).**

$$distance\left(selfGlueDatum, point\left(false\right), point\left(true\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InfiniteCostShortcutBoundary.self_glue_distance_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed singleton self-gluing supplies a forward generator step of cost zero. The chain-distance infimum is therefore at most zero and hence equals zero.

**Theorem 1.4 (Self-gluing orbits are finite).**

$$\forall a \in Sigma\left(Unit \to Bool\right),\; Finite\left(O\left(selfGlueDatum, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InfiniteCostShortcutBoundary.self_glue_orbits_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orbit is a subset of the two-point tagged space, so it is finite.

**Theorem 1.5 (No-generator orbits are finite).**

$$\forall a \in Sigma\left(Unit \to Bool\right),\; Finite\left(O\left(noGeneratorDatum, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InfiniteCostShortcutBoundary.no_generator_orbits_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orbit is a subset of the same two-point tagged space, so it is finite even without generators.

This is a concrete boundary instance. It does not assert a general quotient construction, geodesicity, isometric embedding of the original piece, or any curvature or angle statement. The example records why a finite-cost qualifier is necessary when a chain metric is used to recover an original realization.

## References

- Truth anchor: `D5/S3/Topology/InfiniteCostShortcutBoundary.no_generator_distance_infinite`
- Truth anchor: `D5/S3/Topology/InfiniteCostShortcutBoundary.no_generator_finite_chain_exists`
- Truth anchor: `D5/S3/Topology/InfiniteCostShortcutBoundary.no_generator_orbits_finite`
- Truth anchor: `D5/S3/Topology/InfiniteCostShortcutBoundary.self_glue_distance_zero`
- Truth anchor: `D5/S3/Topology/InfiniteCostShortcutBoundary.self_glue_orbits_finite`
- Dependency: [D5/S3/Topology/FiniteOrbitChainMetric](FiniteOrbitChainMetric.md)
