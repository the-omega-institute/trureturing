# Fixed-seed counts over output orbits

## Abstract

Coordinate fixed counts on finite fibres of an equivariant readout.

**Theorem 1.1 (Fibre sizes and fixed counts are constant on each output orbit).**

$$\forall I \in FiniteIndexTypes,\; \forall T \in \operatorname{ActionTypes}\left(I\right),\; \forall f \in \operatorname{FiniteEquivariantReadouts}\left(I, T\right),\; \exists m \in \operatorname{OrbitSizes}\left(I, T\right),\; \exists z \in \operatorname{OrbitCoordinateCounts}\left(I, T\right),\; \left(\forall o \in \operatorname{Orbits}\left(I, T\right),\; \forall j \in I,\; \operatorname{z}\left(o, j\right) \le \operatorname{m}\left(o\right) \land \operatorname{ModTwo}\left(\operatorname{z}\left(o, j\right)\right) = \operatorname{ModTwo}\left(\operatorname{m}\left(o\right)\right)\right) \land \operatorname{FibreEquations}\left(f, m, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts.orbit_fixed_fibre_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action group for an index type I is the product of copies of the group of order two, with one generator per index. An action type T carries an action of this group. A finite equivariant readout consists of a finite source with an action and a map f commuting with the actions.

The fibre equations say that each output x has m(Orbit(x)) preimages. For coordinate j, the number of those preimages fixed by its generator is z(Orbit(x),j) if the generator fixes x, and zero otherwise. OrbitSizes and OrbitCoordinateCounts are natural-valued functions on orbits and on orbit-coordinate pairs, respectively.

Translating a fibre preserves its size and its fixed counts, since the group is abelian. When a generator fixes x, it acts as an involution on the fibre, so the moved seeds occur in pairs.

**Theorem 1.2 (The size and parity conditions characterize common realizations).**

$$\forall I \in FiniteIndexTypes,\; \forall T \in \operatorname{FiniteActionTypes}\left(I\right),\; \forall m \in \operatorname{OrbitSizes}\left(I, T\right),\; \forall z \in \operatorname{OrbitCoordinateCounts}\left(I, T\right),\; \left(\exists f \in \operatorname{FiniteEquivariantReadouts}\left(I, T\right),\; \operatorname{FibreEquations}\left(f, m, z\right)\right) \Leftrightarrow \left(\forall x \in T,\; \forall j \in I,\; \operatorname{Fixes}\left(j, x\right) \Rightarrow \left(\operatorname{z}\left(\operatorname{Orbit}\left(x\right), j\right) \le \operatorname{m}\left(\operatorname{Orbit}\left(x\right)\right) \land \operatorname{ModTwo}\left(\operatorname{z}\left(\operatorname{Orbit}\left(x\right), j\right)\right) = \operatorname{ModTwo}\left(\operatorname{m}\left(\operatorname{Orbit}\left(x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts.exact_orbit_fibre_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite output action type T, a nonnegative fibre size m on each orbit and a nonnegative fixed count z per orbit and coordinate. The fibre equations have a common finite equivariant realization exactly when each generator that fixes the output satisfies the displayed size and parity conditions.

Above each output, take a common set of paired labels for its orbit and a singleton label if the fibre size is odd. Each coordinate generator swaps the necessary number of label pairs independently. The permutations commute because they act pair by pair. The group simultaneously acts on the underlying output and on these labels.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts.exact_orbit_fibre_counts`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts.orbit_fixed_fibre_counts`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit](CoordinateColourOrbit.md)
