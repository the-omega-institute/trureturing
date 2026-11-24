# Single fibres with three paired neighbours

## Abstract

The energy cost of three paired neighbours

**Theorem 1.1 (An upper bound on the three-contact single fibres).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis.triple_contact_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis.triple_contact_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Delete the main coordinate and fix a projected parity for the paired fibres. Each paired fibre has exactly four single neighbours. The two endpoints supply two neighbours each, and overlap would complete a selected square.

The switching signs give a function supported on the paired fibres. At a single fibre, the signed Huang terms agree, so a single fibre with k paired neighbours contributes k squared to the energy. The Huang square identity gives eight units per paired fibre. Subtracting the single-fibre energy from twice the incidence count shows that the number of one-contact fibres minus three times the number of three-contact fibres equals the nonnegative energy on empty fibres.

An order-preserving reindexing moves the main axis to the first coordinate and preserves the remaining fibre labels. The estimate applies to the selected apexes forced by opposite-parity witnesses in Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis.triple_contact_card_le`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity](Q9OccupiedFibreParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction](../CubicFiftyFourReconstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
