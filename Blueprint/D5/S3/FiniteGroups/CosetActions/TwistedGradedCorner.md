# Homogeneous lines in a twisted graded corner

## Abstract

Inverse-degree pairings and twisted associativity bound the dimensions of the grades. When the total dimension is the group order, every grade is a line.

Let B be a complex vector space with components indexed by a group K. Its bilinear multiplication respects the grading, has unit e, and satisfies twisted associativity on homogeneous triples with a nonzero scalar for each triple of degrees. The identity component is the span of e. Each nonzero homogeneous vector has a nonzero product with some right factor of inverse degree.

**Theorem 1.1 (Spanning an occupied grade).**

Lean statement: `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.grade_eq_span_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.grade_eq_span_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a nonzero vector a in a grade and an inverse-degree vector b with ab a nonzero multiple of e. For any c of the same degree as a, the product bc is a scalar multiple of e. Twisted associativity then identifies a nonzero scalar multiple of c with a scalar multiple of a. This is the spanning argument from Davydov and Simmons, Lemma 2.14. https://arxiv.org/abs/1603.04650

**Theorem 1.2 (Products of nonzero homogeneous vectors).**

Lean statement: `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.homogeneous_mul_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.homogeneous_mul_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero homogeneous x and y, choose an inverse-degree z so that yz is a nonzero multiple of e. Then x(yz) is a nonzero multiple of x. Twisted associativity forces xy to be nonzero.

**Theorem 1.3 (Dimension saturation).**

Lean statement: `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.finrank_grade_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.finrank_grade_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume K is finite and the components form an internal direct sum equal to B. The total dimension is the sum of the component dimensions. Each is at most one by the spanning result, so equality of the total dimension with the group order forces every component to have dimension one.

## References

- Truth anchor: `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.finrank_grade_eq_one`
- Truth anchor: `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.grade_eq_span_singleton`
- Truth anchor: `D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner.homogeneous_mul_ne_zero`
