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

**Theorem 1.4 (Restrictions on distinct product factors).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.independent_restrictions_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.independent_restrictions_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each coordinate at least one of the two restrictions is the whole module. Reordering the two entries at the coordinates where necessary identifies the unrestricted times doubly restricted product with the product of the individually restricted families.

**Theorem 1.5 (Product identity for two separated coefficients).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.separated_coefficients_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.separated_coefficients_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the submodule of alternating forms is preserved by the projections to fixed intersections with a chosen set of indices. Two coefficients with distinct intersections restrict different factors. The unrestricted times doubly restricted forms are equivalent to the product of the two single restrictions.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.exists_split`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.independent_restrictions_product`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.insertion_project`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.separated_coefficients_product`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates.split_with_omitted_faces`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms](UniformCircuitResidueForms.md)
