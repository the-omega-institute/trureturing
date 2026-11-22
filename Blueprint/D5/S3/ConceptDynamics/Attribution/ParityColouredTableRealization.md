# Realize a coloured parity table by a common seed action

## Abstract

Coordinate fixation from coloured parity cell multiplicities.

**Theorem 1.1 (Invariant pair weights and joint fibre sizes).**

$$\operatorname{InvariantWeightsAndCounts}\left(d, k, w, z\right) \Rightarrow \operatorname{RealizedFibresAndCounts}\left(d, k, w, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.weighted_realization_with_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be at least two and let k be a natural number. Let w be a nonnegative integer weight on each output pair, invariant under the common action, with both coloured marginals equal to 2k. At each coordinate, let z be the sum of w modulo two over the output pairs whose two profiles both contain that coordinate. One equivariant seed action with k times 2 raised to the power (d + 1) seeds has those coloured marginals, fixes z(i) seeds at each coordinate i, and has exactly w(a) seeds over every output pair a.

**Theorem 1.2 (Least fixed counts from coloured cell multiplicities).**

$$\operatorname{ColouredMargins}\left(d, k, m\right) \Rightarrow \operatorname{RealizedFibresAndCounts}\left(d, k, m, \operatorname{LeastFibreCounts}\left(d, m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.realize_coloured_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension d is at least two. The table m has a natural-number multiplicity for every even profile, odd profile, and binary left colour. Both right colours use that same multiplicity. Every even profile and left colour has marginal k. Every odd profile has marginal 2k after summing over even profiles and both left colours. The two left-colour entries coincide for every profile other than the full even profile.

A common equivariant seed action has k times 2 raised to the power (d + 1) seeds, with both coloured marginals equal to 2k at every point. At coordinate i its fixed count is twice the sum of each entry modulo two, summed over the cells whose two profiles both contain i and both left colours. For each pair of profiles and any two colours, the joint fibre size is exactly the entry indexed by the profiles and the left colour.

Coordinate shifts preserve each profile. The full even profile also preserves its colour. The multiplicity therefore descends to the output orbit. Within the fibre of any fixed output point the least allowed number of fixed seeds is its size modulo two. The orbit criterion realizes these least counts simultaneously.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.realize_coloured_table`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.weighted_realization_with_fibres`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit](CoordinateColourOrbit.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts](CoordinateFibreCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum](ParitySeedCountSpectrum.md)
