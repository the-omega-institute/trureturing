# Polynomial Fock State Fields

## Abstract

Every complex polynomial Fock state has a creative local field with actual translation.

Y extends the sorted monomial occurrence construction linearly to every polynomial. Each occurrence of X_k contributes the kth divided derivative of the actual current, with explicit right nesting ending in the identity field. No degree cutoff or normal-product associativity is assumed. Locality holds as an endomorphism identity with an order depending only on the two polynomial states. These rank-one formal fields do not assert an actual Monster realization or physical geometry.

**Theorem 1.1 (Every polynomial is created and the quadratic conformal field is actual).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_creation` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Y(1) is the identity field and Y(X_0) is the actual current. For every polynomial p, Y(p)_(−1) applied to the vacuum equals p, and every nonnegative mode kills the vacuum. For every integer n, the nth mode of Y((1/2)X_0^2) is the existing L(n−1). The comparison splits the actual finite Sugawara sum into its two integer-sign halves.

**Theorem 1.2 (The actual L(-1) translates every polynomial field).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_translation` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

L(-1) kills the vacuum. For every polynomial p and every integer n, [L(-1),Y(p)_n]=-n Y(p)_(n−1) as an endomorphism of the same complex polynomial Fock space. The current commutator propagates through divided derivatives, the actual ordered products and the monomial basis. No premise postulates translation of the resulting Y.

**Theorem 1.3 (Every polynomial pair is operator-uniformly local).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_locality` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For every two polynomial states p and q there is a natural N such that the Nth binomial finite difference of [Y(p)_m,Y(q)_n] vanishes for every pair of integer mode indices as an endomorphism. N is selected from field words and the finite polynomial supports, before either index or input vector. The normal-product locality kernel is used by the actual Y.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_creation`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_locality`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_translation`
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProduct](FieldNormalProduct.md)
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProductLocality](FieldNormalProductLocality.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators](PolynomialFockSugawaraCommutators.md)
