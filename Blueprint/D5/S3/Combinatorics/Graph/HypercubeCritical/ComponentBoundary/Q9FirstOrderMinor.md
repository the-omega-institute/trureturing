# First-order certificates for omitted-row minors

## Abstract

A right kernel vector identifies the linear coefficient, and a left kernel vector can certify its nonvanishing.

**Theorem 1.1 (A right kernel vector identifies the determinant coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor.mul_coeff_one_det_pencil_eq_det_updateCol`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor.mul_coeff_one_det_pencil_eq_det_updateCol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and E be square matrices on a finite index set over a commutative ring. If A x = 0, then for every column j, the j-th coordinate of x times the coefficient of X in det(A + X E) equals the determinant obtained from A by replacing column j by E x.

Put M = A + X E over the polynomial ring. Replacing column j by M x multiplies its determinant by x(j), by the determinant law for a linear combination of columns. The kernel equation makes the new column X times E x. Pull out X from that column and compare coefficients of degree one. The constant coefficient on the replacement side is the determinant with the constant matrices, since taking constant coefficients is a ring homomorphism.

**Theorem 1.2 (A nonzero left-right pairing certifies the minor).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor.coeff_one_det_pencil_ne_zero_of_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor.coeff_one_det_pencil_ne_zero_of_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a field, assume A x = 0, yᵀ A = 0, and yᵀ E x ≠ 0. If the columns of A other than j are linearly independent, then the coefficient of X in det(A + X E) is nonzero.

A vector in the kernel of the replacement matrix gives a linear relation among its columns. Pairing with y forces the coefficient of column j to vanish. Independence forces the remaining coefficients to vanish. The replacement determinant is therefore nonzero, so the coefficient identity gives the claim.

Let B(w) be a rational weighted omitted-row matrix with n columns on the selected rows. Along w = w₀ + X h, write B(w) = B(w₀) + X H. Fix a column j and choose n−1 of the selected rows so that the (n−1) × (n−1) submatrix of B(w₀) on those rows and all columns other than j has nonzero determinant. Suppose x is a right-kernel vector of B(w₀) with x(j) = 1. Solve on the pivot rows for the combination of the retained columns that agrees there with H x.

Subtract that column combination from H x to obtain the residual. A left-kernel vector of the full rectangular B(w₀) pairs with this residual just as it pairs with H x, since it annihilates the retained columns. If the pairing is nonzero, some selected row outside the pivot has a nonzero residual. Add that row to the pivot rows and take all n columns to form a square minor.

Let A and E be the restrictions of B(w₀) and H to these n rows. The pivot ensures that the retained columns of A are independent, and A x = 0 by restriction. On the retained columns, express the added row as a combination of the pivot rows. The functional that subtracts this combination of pivot-row coordinates from the added-row coordinate also annihilates column j, since A x = 0 and x(j) = 1. Its value on E x is the residual on the added row. The theorem therefore gives a nonzero linear coefficient of det(A + X E). This polynomial is nonzero at some rational point on the line because it has finitely many roots.

This criterion applies to each choice of rows and direction satisfying the certificate hypotheses. Hong, Wu and Xia's Problem 2 asks whether f₂(Q₉) equals 3 or 4. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor.coeff_one_det_pencil_ne_zero_of_pairing`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor.mul_coeff_one_det_pencil_eq_det_updateCol`
