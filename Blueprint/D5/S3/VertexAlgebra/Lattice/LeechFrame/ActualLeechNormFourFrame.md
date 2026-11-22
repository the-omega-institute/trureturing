# The actual Leech norm-four frame

## Abstract

Twenty-four explicit orthogonal norm-four charges in the actual Leech lattice.

The index is Fin 12 times Bool. The first entry selects the consecutive coordinates 2i and 2i + 1, and the second selects the sign on the latter. Each vector has entries 4 and plus or minus 4 on those coordinates and zero elsewhere. The two directions in a pair have dot product zero. Distinct pairs have disjoint supports. The squared coordinate length is 32, and the lattice form divides the dot product by eight.

The construction uses IntegerLeech.Admissible for GolayEncoder.code and RealLeech.mem_lattice for its unscaled real image. ActualLeechHyperbolic.leechData and leechCoordinates are taken from the same witness of RealLeech.exists_positive_even_unimodular_gram. The proof uses the rank 24 and pairing identity from leech_spec. It has no frame, code, or lattice hypotheses.

**Definition 1.1 (Integral Golay coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.integralVector`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.integralVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use two integer spikes on the chosen coordinate pair.

**Theorem 1.2 (Golay admissibility).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.admissible`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common parity is zero, the half-coordinate residue word is the zero word in the Golay code, and the coordinate sum is zero or eight.

**Definition 1.3 (Actual Leech charges).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.charge`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.charge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pull back the real image of the admissible vector along the integral equivalence leechCoordinates.

**Theorem 1.4 (Coordinates of each charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.coordinates_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.coordinates_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image in the real Golay coordinate space is the unscaled cast of the chosen integral vector.

**Theorem 1.5 (Integral Gram pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.charge_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.charge_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer bilinear pairing is four on equal indices and zero on unequal indices. The two cases are exposed as charge_norm and charge_orthogonal.

**Theorem 1.6 (Complex Gram pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.complex_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.complex_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the images of the charges in the complex current space, the complex bilinear form g has Gram matrix four times the identity.

**Definition 1.7 (Basis of the complex current space).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.complexBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.complexBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Orthogonality with nonzero self-pairings gives linear independence. The number of indices equals the dimension of the current space. The basis vector at each index is the complex image of the specified charge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.admissible`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.charge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.charge_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.complexBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.complex_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.coordinates_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.integralVector`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic](../ActualLeechHyperbolic.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates](../LatticeLightConeCoordinates.md)
