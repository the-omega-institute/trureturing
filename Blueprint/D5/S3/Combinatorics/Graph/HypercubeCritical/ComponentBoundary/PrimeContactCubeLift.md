# The integer lift of the entire signed cube contact neighborhood

## Abstract

The integer lift of the entire signed cube contact neighborhood

**Theorem 1.1 (Two distance-two columns have one occupied and one empty common row).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.common_rows_of_hammingDist_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.common_rows_of_hammingDist_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed products around a Huang square are negative. Coherence at occupied rows rules out two occupied corners. Cancellation with the unit kernel signs rules out two empty corners. The common neighboring rows therefore have opposite classifications.

**Theorem 1.2 (Integer transport extends to every neighboring row).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.exists_row_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.exists_row_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an empty row the two adjacent column exponents agree after adding their respective coordinate basis vectors. The other corner of the square is occupied, where subtracting those basis vectors gives the same lower exponent. This extends the potential to all contact rows regardless of their occupied contact multiplicity.

**Theorem 1.3 (Kernel signs and switching signs agree up to a component sign).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.sign_product_eq_of_reachable`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.sign_product_eq_of_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied and empty equations on a mixed square identify the products of the switching and kernel signs on its two columns. Their ratio is therefore constant along an empty-row path.

**Theorem 1.4 (The integer potential preserves the grade and shifted binary coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.grade_and_parity_of_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.grade_and_parity_of_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gain along an empty contact edge is a difference of two coordinate basis vectors. It preserves the integer coordinate sum. Reducing each coordinate modulo two gives the corresponding cube bit after one global bit translation.

For the two-contact paired-fibre branch of Hong, Wu and Xia's Problem 2, this makes the prime transport a lattice lift of the actual cube neighborhood. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.common_rows_of_hammingDist_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.exists_row_exponent`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.grade_and_parity_of_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift.sign_product_eq_of_reachable`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport](PrimeContactTransport.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
