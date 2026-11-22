# Circuit Coordinates with Zero Weights

## Abstract

Alternating-form equations separated by the indices with zero weight.

**Theorem 1.1 (Weighted insertion preserves the intersection).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.insertion_project`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.insertion_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a set of basis indices whose weights vanish. Keeping the coefficients with one prescribed intersection with that set commutes with insertion of the weighted vector. Only indices outside the chosen set can contribute to the insertion sum, so each contributing face has the same intersection.

**Theorem 1.2 (Product decomposition of the weighted kernel).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.exists_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.exists_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For forms killed by both weighted insertion and a fixed integer, the projections give a linear equivalence with the product of the parts supported on each prescribed intersection. Adding the projected forms recovers the original form.

**Theorem 1.3 (Omitted faces constrain individual factors).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.split_with_omitted_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.split_with_omitted_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Requiring the coefficient of an omitted face to vanish restricts the factor indexed by its intersection with the zero-weight set. Omitted faces with distinct intersections therefore impose equations in different factors of the product.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.exists_split`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.insertion_project`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.split_with_omitted_faces`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms](UniformCircuitResidueForms.md)
