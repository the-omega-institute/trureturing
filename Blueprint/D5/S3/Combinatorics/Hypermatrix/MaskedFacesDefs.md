# Scalar fiber action

## Abstract

Scalar fiber action

**Definition 1.1 (Matrix faces).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Faces`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Faces` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

A pair of matrices with k plus one rows and k columns over F. The first face is indexed by zero and the second by one.

**Definition 1.2 (Both zero masks).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Respects`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Respects` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every row r and column j, the first face vanishes when k plus one minus lambda(j) is at most r, and the second when k plus one minus mu(j) is at most r. Row and column indices start at zero.

**Definition 1.3 (All nonzero combinations over the algebraic closure).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.ClosureFullRank`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.ClosureFullRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every pair a,b in the algebraic closure of F, with at least one nonzero, the linear combination a times the first face plus b times the second has rank k. The original faces are mapped by the algebra map; this condition includes combinations with coefficients outside F.

**Definition 1.4 (Actual masked pencils).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.ActualCarrier`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.ActualCarrier` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The subtype of matrix-face pairs satisfying both literal masks and ClosureFullRank.

**Definition 1.5 (Finite q bracket).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.qBracket`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.qBracket` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The natural number sum of q to the exponent e over all natural e strictly less than n. The empty bracket is zero.

**Definition 1.6 (First standard face).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.E0`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.E0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The entry is one when the row is the column cast into Fin(k plus one), and zero otherwise.

**Definition 1.7 (Second standard face).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.E1`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.E1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The entry is one when the row is the successor of the column, and zero otherwise.

**Definition 1.8 (Left cell coordinates).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.XVariables`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.XVariables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Pairs a less than b of row positions such that sigma(b) is less than sigma(a).

**Definition 1.9 (Right cell coordinates).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.YVariables`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.YVariables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Pairs i less than j of column positions such that pi(j) is less than pi(i).

**Definition 1.10 (Joint independent coordinates).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.CellVariables`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.CellVariables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The disjoint union of the left and right inversion coordinate sets.

**Definition 1.11 (Southeast representative).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellA`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

At row sigma(a) and column b, the entry is one when a equals b, the left coordinate at (a,b) when a is less than b and sigma(b) is less than sigma(a), and zero otherwise.

**Definition 1.12 (Northwest right representative).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellB`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

At row pi(j) and column i, the entry is one when i equals j, the right coordinate at (i,j) when i is less than j and pi(j) is less than pi(i), and zero otherwise.

**Definition 1.13 (Southeast pivot condition).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.SEShape`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.SEShape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every a,b, the entry at row sigma(a) and column b is one on the pivot diagonal, can be free only when a is less than b and sigma(b) is less than sigma(a), and is zero in all other positions.

**Definition 1.14 (Northwest right pivot condition).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.NWRightShape`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.NWRightShape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every i,j, the entry at row pi(j) and column i is one when i equals j, can be free only when i is less than j and pi(j) is less than pi(i), and is zero elsewhere.

**Definition 1.15 (Read both inversion coordinate families).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellRead`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellRead` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The left coordinates read the entry A(sigma(a),b); the right coordinates read B(pi(j),i).

**Definition 1.16 (Coefficient indices).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.CoeffIndex`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.CoeffIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Pairs consisting of a column in Fin(k) and a binary homogeneous degree in Fin(k plus one).

**Definition 1.17 (Integral Koszul coefficient matrix).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientMatrix`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Acknowledgement.* Christine Berkesch Zamaere, Daniel Erman, Manoj Kummini, Steven V. Sam (2013). *Tensor complexes: Multilinear free resolutions constructed from higher tensors*. DOI: [10.4171/JEMS/421](https://doi.org/10.4171/JEMS/421). URL: <https://arxiv.org/abs/1101.4604v5>.

*Commentary.*

For row (j,t) and column (s,r), the entry is delta(t=s) times M0(r,j) plus delta(t=s+1) times M1(r,j). Its size is k times (k plus one). This is the finite coefficient specification used for the boundary-format determinant.

**Definition 1.18 (Homogeneous kernel weights).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientWeight`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The coordinate (j,t) is z(j) times a to the power k minus t times b to the power t.

**Definition 1.19 (Original tensor entries).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.TensorVariable`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.TensorVariable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Triples consisting of a face in Fin(2), row in Fin(k plus one), and column in Fin(k).

**Definition 1.20 (Cayley finite polynomial specification).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientPolynomial`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Acknowledgement.* Christine Berkesch Zamaere, Daniel Erman, Manoj Kummini, Steven V. Sam (2013). *Tensor complexes: Multilinear free resolutions constructed from higher tensors*. DOI: [10.4171/JEMS/421](https://doi.org/10.4171/JEMS/421). URL: <https://arxiv.org/abs/1101.4604v5>.

*Commentary.*

Over the integers, substitute the independent tensor variables into the two faces of coefficientMatrix and take its determinant. Evaluation uses the actual entries of the same matrix-face pair. The sign of the integral normalization has no effect on its nonvanishing over any finite field.

**Definition 1.21 (Two actual general linear factors).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Factors`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Factors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The product of GL(Fin(k plus one),F) and GL(Fin(k),F).

**Definition 1.22 (Standard pencil action).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.factorMap`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.factorMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

A factor pair (A,B) maps to (A E0 B, A E1 B) on the same two faces.

**Definition 1.23 (Scalar fiber action).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.shift`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.shift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

A unit u replaces A by A times the scalar matrix u and B by the scalar matrix u inverse times B.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.ActualCarrier`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.CellVariables`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.ClosureFullRank`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.CoeffIndex`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.E0`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.E1`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Faces`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Factors`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.NWRightShape`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.Respects`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.SEShape`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.TensorVariable`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.XVariables`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.YVariables`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellA`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellB`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.cellRead`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientMatrix`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.coefficientWeight`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.factorMap`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.qBracket`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs.shift`
- Dependency: [D5/S3/Combinatorics/Permutation/CoupledRepairedWeight](../Permutation/CoupledRepairedWeight.md)
