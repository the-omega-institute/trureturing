# Relative primeness of the signed coefficients

## Abstract

The literal orientation of the closing factor is used when isolating the first coordinate.

**Definition 1.1 (Distinguished matching edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.zeroEdge`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.zeroEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinguished edge has index zero in each matching.

**Definition 1.2 (Second coordinate).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.nextCoord`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.nextCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second column survives removal of the first column from the variable set.

**Definition 1.3 (Closing coordinate).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.lastCoord`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.lastCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The last column survives removal of the first column from the variable set.

**Definition 1.4 (Third coordinate).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.middleCoord`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.middleCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third column survives removal of the first column from the variable set.

**Definition 1.5 (Remaining odd endpoints).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.oddRest`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.oddRest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are the odd matching endpoints outside the distinguished edge.

**Definition 1.6 (Remaining even endpoints).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.evenRest`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.evenRest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are the even matching endpoints outside the distinguished edge.

**Definition 1.7 (Odd tail product).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.U`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the oriented factors of the remaining odd edges.

**Definition 1.8 (Even tail product).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.V`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the oriented factors of the remaining even edges.

**Definition 1.9 (Linear coefficient).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.A`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of the first coordinate is the odd tail product minus the even tail product.

**Definition 1.10 (Constant coefficient).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPrimitive.B`

*Formalization.* `D5/S3/Geometry/KozakiKakeiPrimitive.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant coefficient is the last coordinate times the even tail product minus the second coordinate times the odd tail product.

**Theorem 1.11 (The two signed coefficients).**

$$\forall m : \mathbb{N}, 2 \le m \implies \operatorname{isolate}(\operatorname{first}(m),F(m)) = \operatorname{PolynomialC}(A(m)) \cdot \operatorname{PolynomialX} + \operatorname{PolynomialC}(B(m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPrimitive.isolate_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Isolating the first column variable gives the linear polynomial with coefficients A and B.

**Theorem 1.12 (Four-column coefficient).**

$$A(2) = X(\operatorname{lastCoord}(2)) + X(\operatorname{nextCoord}(2)) - 2 \cdot X(\operatorname{middleCoord}(2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPrimitive.signed_four_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linear coefficient is the sum of the last and second variables minus twice the third. Both tail products have one factor.

**Theorem 1.13 (Nonzero relatively prime coefficients).**

$$\forall m : \mathbb{N}, 2 \le m \implies m \neq 3 \implies A(m) \neq 0 \land \operatorname{IsRelPrime}(A(m),B(m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPrimitive.primitive_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Off order six, a common prime must divide the difference between the second and last coordinates. Identifying those two coordinates leaves the linear coefficient nonzero, with a separate specialization at order four.

**Theorem 1.14 (The linear coefficient is a nonunit).**

$$\forall m : \mathbb{N}, 2 \le m \implies \neg\operatorname{IsUnit}(A(m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPrimitive.A_not_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation with every remaining coordinate zero sends each nonempty tail product to zero.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.A`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.A_not_unit`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.B`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.U`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.V`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.evenRest`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.isolate_F`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.lastCoord`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.middleCoord`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.nextCoord`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.oddRest`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.primitive_coefficients`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.signed_four_coefficient`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPrimitive.zeroEdge`
- Dependency: [D5/S3/Geometry/KozakiKakeiAffine](KozakiKakeiAffine.md)
