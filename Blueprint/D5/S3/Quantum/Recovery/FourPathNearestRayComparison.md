# Four-path nearest-ray comparison

## Abstract

The nearest-ray Kraus estimate separates trace-defect and coordinate-distance errors and preserves the source constants after finite summation.

**Theorem 1.1 (Finite-family error aggregation).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNearestRayComparison.finite_family_error_aggregation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathNearestRayComparison.finite_family_error_aggregation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of matrix errors K - B = E + F, if the squared norms of E and F are bounded by 2τ and c d² termwise, then the summed squared error is bounded by 4Στ + 2cΣd².

The proof applies the squared triangle estimate pointwise and then distributes the finite sums.

**Theorem 1.2 (Selected mass bounds and defect).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathNearestRayComparison.selected_mass_bounds_and_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathNearestRayComparison.selected_mass_bounds_and_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative coordinate weights with unit total mass, assigning each index to its larger coordinate yields selected masses in [0,1]. The two complementary masses sum to the finite sum of coordinatewise minima.

The proof partitions each coordinate by the selected Boolean assignment and uses the completeness sums.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNearestRayComparison.finite_family_error_aggregation`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathNearestRayComparison.selected_mass_bounds_and_defect`
- Dependency: [D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder](FourPathWeightedEqualityRemainder.md)
