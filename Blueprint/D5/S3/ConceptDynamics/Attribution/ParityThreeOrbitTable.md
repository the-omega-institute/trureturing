# Three-coordinate orbit tables

## Abstract

Integer orbit tables for uniform coloured parity in three coordinates.

**Theorem 1.1 (Orbit table feasibility is equivalent to realization).**

$$\forall k \in Nat,\; \forall z \in \operatorname{CountVectors}\left(3\right),\; \operatorname{Realizable}\left(1, k, z\right) \Leftrightarrow \operatorname{HasOrbitTable}\left(k, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityThreeOrbitTable.exact_orbit_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CountVectors(3) consists of natural-valued functions on Fin(3). Realizable(1,k,z) requires an equivariant seed action on 16k seeds, uniform coloured even and odd parity marginals, and fixed counts z.

Order the even words as 000, 011, 101, 110 and the odd words as their complements. HasOrbitTable(k,z) stores one multiplicity per orbit and one entry per orbit and coordinate. An entry gives the fixed count per output point when that coordinate generator fixes the orbit pointwise. The all-ones odd column has two orbits of size two at each row, one for each right colour. Every other cell has one orbit of size four.

At each row the sum of the two special multiplicities plus twice the sum of the ordinary multiplicities is 2k. Each ordinary column and each special colour column have multiplicity sum k. Each coordinate entry is at most its multiplicity and has the same parity. To obtain z at a coordinate, keep just the entries whose two words have bit one there and weight each entry by its orbit size.

An implementation gives the table by counting fibres. The converse uses the simultaneous orbit fibre criterion. Entries at coordinates moved by the output action do not enter the totals.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityThreeOrbitTable.exact_orbit_table`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit](CoordinateColourOrbit.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts](CoordinateFibreCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedBudget](ParitySeedBudget.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum](ParitySeedCountSpectrum.md)
