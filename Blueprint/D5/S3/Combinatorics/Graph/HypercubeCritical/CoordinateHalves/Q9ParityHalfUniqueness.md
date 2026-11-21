# Signed coordinate cuts

## Abstract

Reconstruction from one signed parity half of the nine-cube

**Theorem 1.1 (One parity in one coordinate half determines an integer Huang 3-eigenvector with values in {-1, 0, 1}).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ParityHalfUniqueness.eigenvector_eq_of_agree_on_parity_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ParityHalfUniqueness.eigenvector_eq_of_agree_on_parity_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a coordinate and a parity. Suppose two integer eigenvectors with eigenvalue 3 and entries in {-1, 0, 1} agree on that parity in one coordinate half. At a vertex of the same parity in the other half, evaluate the difference of the Huang equations at its axial neighbor. Each transverse term is already known, since a transverse flip preserves the coordinate bit and returns to the prescribed parity. The only remaining coefficient is an axial sign times the entry difference, which lies between -2 and 2. Its divisibility by 3 forces it to vanish.

The equations on the opposite parity recover its values by dividing the now known signed neighbor sums by 3. For the candidate in Hong, Wu and Xia's Problem 2 whose 72-point component lies on two consecutive Hamming layers, the known parity half is the signed link of a coordinate in the lower layer. The reconstruction allows a search over that link alone. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ParityHalfUniqueness.eigenvector_eq_of_agree_on_parity_half`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](../ComponentBoundary/Q9IsotropicHuang.md)
