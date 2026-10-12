# Special orthogonal bilinear dimension obstruction

## Abstract

A dimension obstruction for antisymmetric bilinear operations under all rotations.

Let I be an arbitrary finite coordinate set. The carrier is the standard real vector space of functions on I, and the symmetry group is the entire special orthogonal matrix group. A nonzero antisymmetric bilinear operation from two vectors to one vector, equivariant under every element of that group, requires exactly three coordinates.

The proof uses half-turns changing the signs of exactly two coordinates. Repeated input coordinates give zero coefficients. Repeated output coordinates are excluded by a half-turn in the input plane. For three distinct coordinates outside dimension three, a fourth coordinate allows a half-turn fixing both inputs and negating the output coefficient.

This is a necessary dimension condition. It does not construct or classify the operations in dimension three, identify an arbitrary inner product space with this coordinate model, or assert any physical space dimension. Replacing the full group by a smaller symmetry group changes the hypotheses.

**Definition 1.1 (Coordinate signs of a half-turn).**

Lean statement: `D5/S3/Geometry/EvenSignTensorObstruction.coordinateSign`

*Formalization.* `D5/S3/Geometry/EvenSignTensorObstruction.coordinateSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected two coordinates have sign minus one; every other coordinate has sign one. Distinct selected coordinates yield determinant one.

**Theorem 1.2 (Third-order tensor obstruction).**

Lean statement: `D5/S3/Geometry/EvenSignTensorObstruction.tensor_eq_zero_of_card_ne_three`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EvenSignTensorObstruction.tensor_eq_zero_of_card_ne_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real coefficient array c indexed by three coordinates vanishes if c(i,i,k) is always zero, every pair-coordinate sign flip preserves the array, and the number of coordinates differs from three. The empty coordinate set is included.

**Theorem 1.3 (Nonzero equivariant bilinearity requires three coordinates).**

Lean statement: `D5/S3/Geometry/EvenSignTensorObstruction.special_orthogonal_equivariant_bilinear_card_eq_three`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EvenSignTensorObstruction.special_orthogonal_equivariant_bilinear_card_eq_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For B(u,v) = -B(v,u), real bilinearity and equivariance B(Ru,Rv) = R B(u,v) for every special orthogonal R imply that nonzero B is possible only when the cardinality of I is three. Diagonal half-turns are genuine elements of the full group; the tensor conclusion forces B to vanish on every basis pair.

## References

- Truth anchor: `D5/S3/Geometry/EvenSignTensorObstruction.coordinateSign`
- Truth anchor: `D5/S3/Geometry/EvenSignTensorObstruction.special_orthogonal_equivariant_bilinear_card_eq_three`
- Truth anchor: `D5/S3/Geometry/EvenSignTensorObstruction.tensor_eq_zero_of_card_ne_three`
