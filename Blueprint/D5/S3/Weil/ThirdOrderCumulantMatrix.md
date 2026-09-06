# Third-Order Cumulant Matrix

## Abstract

Third-order cumulants define an explicit positive matrix whose determinant is the reversed cubic.

**Definition 1.1 (Typed third-order cumulant data).**

Lean statement: `D5/S3/Weil/ThirdOrderCumulantMatrix.ThirdOrderCumulants`

*Formalization.* `D5/S3/Weil/ThirdOrderCumulantMatrix.ThirdOrderCumulants` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The model records the second, fourth, and sixth cumulants as real numbers.

**Definition 1.2 (Strict cubic discriminant condition).**

Lean statement: `D5/S3/Weil/ThirdOrderCumulantMatrix.CubicDiscriminantCondition`

*Formalization.* `D5/S3/Weil/ThirdOrderCumulantMatrix.CubicDiscriminantCondition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed inequalities require u = -chi4 to be positive and 3 chi6^2 < 100 u^3. They imply that both squared off-diagonal coefficients b1 and b2 are strictly positive.

**Definition 1.3 (Positive root condition).**

Lean statement: `D5/S3/Weil/ThirdOrderCumulantMatrix.HasPositiveCubicRoots`

*Formalization.* `D5/S3/Weil/ThirdOrderCumulantMatrix.HasPositiveCubicRoots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every real root of the centered cubic q3 is required to be strictly positive. This is an explicit premise for this slice; no residual-open theorem is imported.

**Definition 1.4 (The explicit three-by-three matrix).**

Lean statement: `D5/S3/Weil/ThirdOrderCumulantMatrix.k3Matrix`

*Formalization.* `D5/S3/Weil/ThirdOrderCumulantMatrix.k3Matrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Formula (24) is represented as a real symmetric tridiagonal matrix with center mu, displacement r, and off-diagonal entries sqrt(b1) and sqrt(b2).

**Theorem 1.5 (The matrix has the centered cubic as characteristic polynomial).**

$$\forall c, CubicDiscriminantCondition\left(c\right) \Rightarrow charpoly\left(k3Matrix\left(c\right)\right) = q3\left(c\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ThirdOrderCumulantMatrix.k3_charpoly_eq_q3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the three-by-three determinant and using the discriminant inequalities to rewrite both square-root squares identifies the characteristic polynomial coefficient by coefficient with q3.

**Theorem 1.6 (The cubic data certify all leading minors and positive definiteness).**

$$\forall c, {{CubicDiscriminantCondition\left(c\right)} \land {HasPositiveCubicRoots\left(c\right)}} \Rightarrow {{0 < leadingPrincipalMinorOne\left(k3Matrix\left(c\right)\right)} \land {{0 < leadingPrincipalMinorTwo\left(k3Matrix\left(c\right)\right)} \land {{0 < det\left(k3Matrix\left(c\right)\right)} \land {PosDef\left(k3Matrix\left(c\right)\right)}}}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ThirdOrderCumulantMatrix.K3_posdef_from_cubic_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The computed characteristic polynomial sends every Hermitian eigenvalue of K3 to a root of q3. The positive-root premise therefore makes every eigenvalue strictly positive, which proves that K3 is positive definite.

Positive definiteness is retained by the one-by-one and two-by-two leading submatrices and makes the full determinant positive. Thus the same witness records all three strict Sylvester minors on the typed cumulant object.

**Theorem 1.7 (The centered cubic reverses to the determinant polynomial).**

$$\forall c, \forall v, CubicDiscriminantCondition\left(c\right) \Rightarrow det\left(1 + v \cdot k3Matrix\left(c\right)\right) = eval\left(p3\left(c\right), v\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ThirdOrderCumulantMatrix.k3_determinant_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A direct determinant expansion gives det(I + v K3) = p3(v). The same b1 and b2 identities used in the characteristic-polynomial calculation remove the square roots.

**Theorem 1.8 (The third-order positive-matrix bridge).**

$$\forall c, \forall v, {{CubicDiscriminantCondition\left(c\right)} \land {HasPositiveCubicRoots\left(c\right)}} \Rightarrow {{PosDef\left(k3Matrix\left(c\right)\right)} \land {det\left(1 + v \cdot k3Matrix\left(c\right)\right) = eval\left(p3\left(c\right), v\right)}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ThirdOrderCumulantMatrix.third_order_cumulant_positive_matrix_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For typed cumulant data satisfying the strict discriminant and positive-root conditions, formula (24) is positive definite and its determinant polynomial is exactly the coefficient reversal p3. No Fibonacci-weight, six-position-chain, or arbitrary higher-order positivity assertion is included.

## References

- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.CubicDiscriminantCondition`
- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.HasPositiveCubicRoots`
- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.K3_posdef_from_cubic_discriminant`
- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.ThirdOrderCumulants`
- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.k3Matrix`
- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.k3_charpoly_eq_q3`
- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.k3_determinant_reversal`
- Truth anchor: `D5/S3/Weil/ThirdOrderCumulantMatrix.third_order_cumulant_positive_matrix_reversal`
