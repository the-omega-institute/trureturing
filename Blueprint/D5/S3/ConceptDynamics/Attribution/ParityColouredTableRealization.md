# Realize a coloured parity table by a common seed action

## Abstract

Coordinate fixation from coloured parity cell multiplicities.

**Theorem 1.1 (Least fixed counts from coloured cell multiplicities).**

$$\operatorname{ColouredMargins}\left(d, k, m\right) \Rightarrow \operatorname{RealizableCounts}\left(d, k, \operatorname{LeastFibreCounts}\left(d, m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.realize_coloured_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension d is at least two. The table m has a natural-number multiplicity for every even profile, odd profile, and binary left colour. Both right colours use that same multiplicity. Every even profile and left colour has marginal k. Every odd profile has marginal 2k after summing over even profiles and both left colours. The two left-colour entries coincide for every profile other than the full even profile.

A common equivariant seed action has k times 2 raised to the power (d + 1) seeds, with both coloured marginals equal to 2k at every point. At coordinate i its fixed count is twice the sum of each entry modulo two, summed over the cells whose two profiles both contain i and both left colours.

Coordinate shifts preserve each profile. The full even profile also preserves its colour. The multiplicity therefore descends to the output orbit. Within the fibre of any fixed output point the least allowed number of fixed seeds is its size modulo two. The orbit criterion realizes these least counts simultaneously.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.realize_coloured_table`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit](CoordinateColourOrbit.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityFourSparseCounts](ParityFourSparseCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum](ParitySeedCountSpectrum.md)
