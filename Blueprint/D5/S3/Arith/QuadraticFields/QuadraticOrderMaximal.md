# QuadraticOrderMaximal

## Abstract

A squarefree quadratic-order discriminant forces integral coordinates: trace and norm put the imaginary coordinate in Z, then integral closedness of Z handles the real coordinate. This identifies the order with the true ring of integers. For p=3 mod4 the discriminant is -p and the field is Q(sqrt(-p)). The unit norm is a positive definite integral form; p>3 leaves only the two units.

A squarefree quadratic-order discriminant forces integral coordinates: trace and norm put the imaginary coordinate in Z, then integral closedness of Z handles the real coordinate. This identifies the order with the true ring of integers. For p=3 mod4 the discriminant is -p and the field is Q(sqrt(-p)). The unit norm is a positive definite integral form; p>3 leaves only the two units.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Theorem 1.1 (integer_of_squarefree_mul_sq_integral).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integer_of_squarefree_mul_sq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integer_of_squarefree_mul_sq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

A squarefree integer cannot cancel a nontrivial square denominator.

**Theorem 1.2 (integral_coordinates).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integral_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integral_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Every integral element of a squarefree-discriminant quadratic order has integral coordinates. The discriminant here is that of the order, not an assumed field discriminant.

**Theorem 1.3 (isIntegralClosure_of_squarefree_discr).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.isIntegralClosure_of_squarefree_discr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.isIntegralClosure_of_squarefree_discr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Maximality of the actual quadratic order, expressed as an integral-closure predicate.

**Theorem 1.4 (algebra_trace_eq).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.algebra_trace_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.algebra_trace_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The coordinate trace agrees with the algebra trace.

**Theorem 1.5 (basis_discr).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.basis_discr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.basis_discr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The order discriminant is the discriminant of its actual integral basis.

**Theorem 1.6 (units_eq_one_or_neg_one).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.units_eq_one_or_neg_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.units_eq_one_or_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Negative quadratic orders of discriminant at most minus seven have only the two units. This deliberately excludes the extra-unit orders of discriminants minus three and minus four.

**Definition 1.7 (ringOfIntegersEquiv).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.ringOfIntegersEquiv`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.ringOfIntegersEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The concrete order is isomorphic to the maximal ring of integers, with its actual integral-closure meaning. No class number is defined by coordinates or a character sum.

**Theorem 1.8 (numberField_discr).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.numberField_discr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.numberField_discr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The genuine number-field discriminant of a squarefree-discriminant quadratic order.

**Definition 1.9 (orderA).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.orderA`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.orderA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The integral generator satisfies omega squared minus omega plus (p+1)/4 equals zero.

**Definition 1.10 (Field).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.Field`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.Field` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary.Field supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Theorem 1.11 (order_discr).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.order_discr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.order_discr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary.order_discr supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Definition 1.12 (sqrtFieldEquiv).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.sqrtFieldEquiv`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.sqrtFieldEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Identification with the standard algebra generated by a square root of minus p.

**Theorem 1.13 (field_discr).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.field_discr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.field_discr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The maximal-order discriminant, with the actual NumberField definition.

**Definition 1.14 (maximalOrderEquiv).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.maximalOrderEquiv`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.maximalOrderEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The actual maximal order, rather than the potentially nonmaximal square-root order.

**Theorem 1.15 (integral_unit_eq_one_or_neg_one).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integral_unit_eq_one_or_neg_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integral_unit_eq_one_or_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The extra-unit exception is excluded by p greater than three.

## References

- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.Field`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.algebra_trace_eq`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.basis_discr`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.field_discr`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integer_of_squarefree_mul_sq_integral`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integral_coordinates`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.integral_unit_eq_one_or_neg_one`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.isIntegralClosure_of_squarefree_discr`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.maximalOrderEquiv`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.numberField_discr`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.orderA`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.order_discr`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.ringOfIntegersEquiv`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.sqrtFieldEquiv`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal.units_eq_one_or_neg_one`
