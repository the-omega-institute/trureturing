# The Actual Imaginary Quadratic Field

## Abstract

For primes r congruent to five modulo eight, the actual field Q(sqrt(-r)) has maximal order Z[sqrt(-r)] and negative fundamental discriminant -4r. Its maximal-order units, signature, regulator, torsion and genuine zeta residue are determined without defining the class number by a finite sum.

This supplies the actual-field and maximal-order portion of the historical Ma–Zhang sign criterion. The signed finite-character class-number formula is established separately in MercaImaginaryClassNumber; it is not asserted by this field construction. The note's byline, CC BY 4.0 license, Farland attribution and classical sources are retained in the linked Library entry. The source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629; no validated audit status is claimed.

**Definition 1.1 (The square-root field).**

Lean statement: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.Field`

*Formalization.* `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.Field` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Field r is QuadraticAlgebra over the rationals with generator squared equal to minus r. Its discriminant is negative, hence nonsquare, so the algebra is a genuine degree-two number field. No supplied class number parameter occurs in this definition.

**Definition 1.2 (The actual integral closure).**

Lean statement: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.maximalOrderEquiv`

*Formalization.* `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.maximalOrderEquiv` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For each prime r congruent to five modulo eight, this integer algebra equivalence identifies Z[sqrt(-r)] with the actual ring of integers. The proof does not apply the squarefree-order-discriminant theorem to -4r. Integral trace and norm first give integral twice-real and twice-imaginary coordinates. Squarefreeness of minus r eliminates a square denominator, and the norm equation modulo four forces both doubled coordinates even.

**Theorem 1.3 (Discriminant, fundamental status and units).**

Lean statement: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.field_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.field_structure` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r congruent to five modulo eight, NumberField.discr of this actual field is -4r and is a fundamental discriminant. An element is integral precisely when both square-root coordinates are integers. Every unit of the actual maximal order is one or minus one. The discriminant is computed from its transported integral basis, and the norm x squared plus r times y squared determines the units.

**Theorem 1.4 (Signature, regulator and class-number residue).**

Lean statement: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.field_invariants`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.field_invariants` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The actual field has zero real places, one complex place, unit rank zero, regulator one and torsion order two. Its genuine Dedekind-zeta residue is pi times NumberField.classNumber divided by twice sqrt(r). This class number is the cardinality of the ideal class group of the ring of integers. A real embedding would produce a real square equal to minus r, so no such embedding exists. The rank-zero regulator and the proved maximal-order unit description discharge the constants in Mathlib's actual residue formula.

## References

- Truth anchor: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.Field`
- Truth anchor: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.field_invariants`
- Truth anchor: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.field_structure`
- Truth anchor: `D5/S3/Arith/QuadraticFields/MercaImaginaryQuadratic.maximalOrderEquiv`
- Dependency: [D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal](QuadraticOrderMaximal.md)
