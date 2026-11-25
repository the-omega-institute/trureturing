# Equal spectra and different rational coordinate counts

## Abstract

Cospectral rational unit Gram matrices with different minimum ambient dimensions.

**Definition 1.1 (Two disjoint weighted edges).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.pairedEdges`

*Formalization.* `D5/S3/Quantum/AURICOmega/RationalGramCospectral.pairedEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal entries are one. A pair of disjoint edges has weight twice the parameter and all other off-diagonal entries equal the parameter.

**Definition 1.2 (An isolated direction and a triangle).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.triangleBlock`

*Formalization.* `D5/S3/Quantum/AURICOmega/RationalGramCospectral.triangleBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal entries are one. The three edges in the triangle have weight twice the parameter. The other off-diagonal entries are zero.

**Definition 1.3 (Exact rational Gram realization).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.RealizableIn`

*Formalization.* `D5/S3/Quantum/AURICOmega/RationalGramCospectral.RealizableIn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix is the product of a rational rectangular matrix with its transpose. The number of columns is the ambient dimension.

**Theorem 1.4 (Six- and seven-coordinate thresholds on a conic).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.thresholds_on_conic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/RationalGramCospectral.thresholds_on_conic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take rational numbers u and v with five times the square of u plus seven times the square of v equal to three. Set the parameter to one quarter of the difference between five times the square of u and one. The two Gram matrices have identical characteristic polynomials with eigenvalues one plus four times the parameter, one, and one minus twice the parameter with multiplicity two. The paired-edge matrix fits in n rational coordinates exactly when n is at least seven. The triangle-block matrix fits exactly when n is at least six.

Rational eigenbases give the common characteristic polynomial. The conic allows rational rescaling to fixed quadratic forms. At the base point both examples have explicit orthogonal Gram factors at their respective thresholds. Aligning a partial frame with the same Gram data reduces both dimension lower bounds to ternary equations. A descent modulo seven excludes the paired-edge form in six coordinates. The three-square obstruction excludes the triangle-block form in five. Appending zero coordinates preserves each realization.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.RealizableIn`
- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.pairedEdges`
- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.thresholds_on_conic`
- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalGramCospectral.triangleBlock`
