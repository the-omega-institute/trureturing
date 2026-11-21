# Equivariant seed counts on table orbits

## Abstract

Integer counts of events under equivariant maps to a finite set.

**Theorem 1.1 (Orbit multiplicities give equivariant copies).**

$$C(A) = \sum_{O} c(A,O) n(O)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts.realize_orbit_copy_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group act on a finite set T. For each orbit O, prescribe a nonnegative integer n(O) giving the number of copies of every element in O. There is a finite seed set with a group action and an equivariant map to T. A seed is fixed by a subgroup exactly when its image is. For any event A in T, its number of seed preimages is the displayed sum.

The action transports the underlying element and preserves the copy index. This construction includes zero multiplicities and empty sets.

**Theorem 1.2 (Every equivariant seed map has orbit multiplicities).**

$$C(A) = \sum_{O} c(A,O) n(O)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts.count_seed_fibers_by_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group act on finite sets S and T, and let f from S to T be equivariant. There is one nonnegative integer n(O) per orbit of T such that the seed count of each event A is the displayed sum.

A group element transports the seed fiber over t bijectively to the fiber over its translate. Hence the fiber size is constant on each orbit. Equivariance is used in this step. For a two-element orbit, a map from a singleton to just one element has unequal fiber sizes.

**Theorem 1.3 (The integer fiber characterizes exact equivariant event counts).**

$$(\exists n \geq 0, \operatorname{M}\left(n\right) = kw) \iff (\exists S, f, \operatorname{Equivariant}\left(f\right) \land \operatorname{ReflectsFixedness}\left(f\right) \land (\forall i, \operatorname{C}\left(S, f, \operatorname{E}\left(i\right)\right) = kw_{i}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts.orbit_event_counts_match_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group act on a finite table set T. Choose a finite indexed family of events E(i) in T and an integer target vector w. The additive map M has entry M(i, O) equal to the size of the intersection of E(i) with orbit O. Fix a natural degree k.

The fiber at k w contains a nonnegative integer vector exactly when there exist a finite seed set S with a group action and an equivariant map f from S to T that realizes the displayed event counts. For every subgroup H and seed s, H fixes s exactly when H fixes f(s).

A vector in the fiber gives the number of copies of each table in its orbit, with the group action preserving the copy index. In the other direction equivariance transports seed fibers along the orbit, so the fiber cardinalities give a single nonnegative vector that satisfies every event equation together. Degree zero allows an empty seed set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts.count_seed_fibers_by_orbit`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts.orbit_event_counts_match_fiber`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts.realize_orbit_copy_counts`
- Dependency: [D5/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees](../../Combinatorics/NumericalSemigroup/IntegerFiberDegrees.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/UniformTableCalibration](UniformTableCalibration.md)
