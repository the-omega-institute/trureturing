# Factorial Polynomial Fock Metric

## Abstract

The arbitrary-variable factorial polynomial Fock metric and creation-derivative pairing.

This module constructs a factorial Hermitian form on arbitrary-variable polynomials and proves the creation/derivative pairing. Scoped compilation, axiom closure and registration assessment are separate evidence from content admission, freeze and CI. The retained statements and 31 normalized declaration bodies come from the sealed 402-line supplier; inner_monomial_left has the disclosed direct repr_self proof edit. The supplier is TransientFactorialFockMetric.lean, SHA-256 0e0b1086fd2edacbc9ef87ddc2f9e105d48f0c61820e88f1e1e72a1a1a82a2a1. The supplier credits its coefficient-embedding architecture to ActualHalfFockHilbertSource; this task reads only the designated generic supplier and imports no transient application.

The factorial normalization is classical symmetric/Bargmann Fock normalization, not a literature novelty claim. AssessedProvenance.FromRepo below refers to the transported formal proof source and its Mathlib reuse, not authorship of the classical normalization. No external literature search was authorized here. Mathlib supplies monomial bases, basis rescaling, partial derivatives, finite-support products and the standard l2 Hilbert basis.

The retained substantive theorem is the all-polynomial creation/derivative pairing. Other retained theorem declarations organize its proof or the positive Core construction and have exact current source consumers; they are not claimed as separate new mathematical results. Unused applications, forwarding aliases and boundary checks are absent from this canonical module.

**Definition 1.1 (Occupation indices).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.Occupation`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.Occupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finitely supported natural occupation on an arbitrary variable type sigma. Sigma need not be finite, countable or inhabited.

**Definition 1.2 (Exact polynomial carrier).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.Polynomial`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.Polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is exactly Mathlib MvPolynomial sigma Complex, rather than a scalar or basis-vector replacement.

**Definition 1.3 (Ambient occupation Hilbert space).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.Hilbert`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.Hilbert` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient space is Mathlib l2 on all occupations with complex scalar values. Only finitely supported polynomial vectors are embedded; no analytic operator domain is asserted.

**Definition 1.4 (Factorial occupation weight).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.weight`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight of d is the finite product of factorial(d(i)) over its support. The empty product is one. This is the classical symmetric or Bargmann Fock normalization.

**Theorem 1.5 (Positive diagonal weights).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.weight_pos`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.weight_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every occupation weight is strictly positive. The supplier uses Nat.factorial_pos and Finset.prod_pos; scale_ne_zero consumes this helper.

**Theorem 1.6 (Enlarging the product index set).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.weight_eq_prod`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.weight_eq_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupation product can be evaluated on any finite superset of its support because factorial(0)=1. This direct Finsupp.prod_of_support_subset helper is consumed in weight_add_single.

**Theorem 1.7 (The factorial shift recurrence).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.weight_add_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.weight_add_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding one quantum at i multiplies the occupation weight by d(i)+1. The proof compares products over insert i d.support and their common erased product. The all-polynomial pairing proof consumes this exact recurrence.

**Definition 1.8 (Square-root factorial scale).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.scale`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.scale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scale is the complex image of the nonnegative real square root of the natural occupation weight.

**Theorem 1.9 (Invertible scale).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.scale_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.scale_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity of the factorial product makes the scale nonzero. scaleUnit consumes this helper; no positivity hypothesis is supplied by a caller.

**Theorem 1.10 (Real scale under conjugation).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.conj_scale`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.conj_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale is fixed by complex conjugation. inner_monomial_left consumes this normalization helper.

**Theorem 1.11 (Square of the scale).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.scale_mul_self`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.scale_mul_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of two scales equals the complex cast of the occupation weight. inner_monomial_left consumes Real.mul_self_sqrt through this helper.

**Definition 1.12 (Scale as a unit).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.scaleUnit`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.scaleUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonzero scale is packaged as a complex unit for Mathlib basis rescaling.

**Definition 1.13 (The rescaled monomial basis).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.scaledBasis`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.scaledBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib Module.Basis.unitsSMul rescales the exact monomial basis by the factorial square-root units.

**Definition 1.14 (An algebraic diagonal equivalence).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basis equivalence sends each monomial basis vector to its square-root-factorial multiple. It is an algebraic complex linear equivalence, with no boundedness or algebra-homomorphism assertion.

**Theorem 1.15 (Diagonal action on the basis).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof directly uses Module.Basis.equiv_apply and unitsSMul_apply. diagonal_monomial consumes this helper.

**Theorem 1.16 (Diagonal action with coefficients).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal equivalence multiplies an arbitrary monomial coefficient by scale(d). diagonal_coeff and embedding_monomial consume this helper.

**Theorem 1.17 (Diagonal action on every coefficient).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial induction in the preserved supplier body computes the diagonal coefficient for every polynomial. This helper is conservatively treated as a consumed basis-coordinate calculation, with pinned Basis.repr_unitsSMul recorded as related reuse.

**Definition 1.18 (The standard l2 Hilbert basis).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.hilbertBasis`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.hilbertBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HilbertBasis.ofRepr applied to the identity linear isometry equivalence supplies the standard occupation-indexed orthonormal basis.

**Definition 1.19 (Unweighted coefficient embedding).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The monomial basis representation followed by finite linear combination in the standard Hilbert basis gives a complex linear map into actual l2.

**Theorem 1.20 (Embedding a monomial basis vector).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib repr_self and linearCombination_single compute the unweighted basis image. coefficientEmbedding_monomial consumes this helper.

**Theorem 1.21 (Unweighted injectivity).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Linear independence of the Hilbert basis makes its finitely supported linear combination injective; composing with the monomial basis representation gives this helper, consumed by embedding_injective.

**Theorem 1.22 (Embedding a monomial with coefficient).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unweighted map sends monomial(d,a) to a times the standard Hilbert vector at d. embedding_monomial consumes this linearity helper.

**Theorem 1.23 (Unweighted coordinate identity).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hilbert basis coordinate of the unweighted image is exactly the original polynomial coefficient. embedding_coeff consumes the Mathlib orthonormal inner-right finite-combination calculation.

**Definition 1.24 (Factorial coefficient embedding).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.embedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual complex linear embedding is coefficientEmbedding composed with diagonal. Its d-coordinate is sqrt(weight(d)) times coeff(d,p). It has an injectivity proof, not an assumed positive form.

**Theorem 1.25 (Injectivity of the factorial embedding).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composition of the unweighted injection with the diagonal linear equivalence gives injectivity. The definite field of core consumes it on the live proof path.

**Theorem 1.26 (Weighted coordinates).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every polynomial p and occupation d, the actual l2 image has coordinate scale(d)*coeff(d,p). The monomial pairing proof consumes this helper.

**Theorem 1.27 (Weighted monomial vectors).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex a, the weighted image of monomial(d,a) is scale(d)*a times the standard Hilbert basis vector. inner_monomial_left consumes this helper.

**Definition 1.28 (Factorial Hermitian form).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.inner`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.inner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The form is the actual Mathlib l2 inner product of the two weighted coefficient images. It is conjugate linear in its first argument and linear in its second argument.

**Definition 1.29 (Positive Mathlib inner product Core).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.core`

*Formalization.* `D5/S3/VertexAlgebra/FactorialFockMetric.core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source constructs an actual InnerProductSpace.Core Complex on the exact polynomial carrier using induced inner-product infrastructure and proves definiteness by embedding injectivity. The seminorm and inner-product instances used during this construction are local; this file installs no global competing instance.

**Theorem 1.30 (Additivity used by polynomial induction).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.inner_add_first`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.inner_add_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Additivity in the first argument follows from the linear embedding and Mathlib inner_add_left. The addition branch of mul_X_pderiv_pairing consumes this helper.

**Theorem 1.31 (One monomial against any polynomial).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.inner_monomial_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.inner_monomial_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,a,q, the form on monomial(d,a) and q is weight(d)*conj(a)*coeff(d,q). The proof computes the actual Hilbert-basis coordinate directly with repr_self and removes the two square-root scales. This consumed helper retains arbitrary q and arbitrary complex a.

**Theorem 1.32 (Creation and derivative on all polynomials).**

Lean statement: `D5/S3/VertexAlgebra/FactorialFockMetric.mul_X_pderiv_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FactorialFockMetric.mul_X_pderiv_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sigma, i:sigma and arbitrary polynomials p,q, inner(X(i)*p,q)=inner(p,pderiv(i,q)). The supplier proof uses polynomial induction in p; its monomial branch uses the exact factorial shift recurrence and pinned MvPolynomial.coeff_pderiv. No desired pairing or positivity statement appears as a hypothesis.

For reuse with the existing original polynomial VOA carrier, specialize sigma to Nat; for finite-colour half modes one may instead use a colour-times-mode type. That substitution only identifies the polynomial carrier. PolynomialFockSugawaraSupport defines annihilate(k)=(k+1)*pderiv(k), while this metric pairs bare X(k) with bare pderiv(k): the mode factor k+1 must still be reconciled by a justified coordinate rescaling or a different mode-weighted metric. There is no current, Virasoro, ground or charged unitarity conclusion here. No maximal analytic adjoint, completion/density theorem, convergence statement, Monster construction, full string theory, spacetime dynamics, or AdS/CFT result is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.Hilbert`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.Occupation`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.Polynomial`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_basis`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_injective`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.coefficientEmbedding_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.conj_scale`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.core`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_basis`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.diagonal_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_injective`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.embedding_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.hilbertBasis`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.inner`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.inner_add_first`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.inner_monomial_left`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.mul_X_pderiv_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.scale`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.scaleUnit`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.scale_mul_self`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.scale_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.scaledBasis`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.weight`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.weight_add_single`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.weight_eq_prod`
- Truth anchor: `D5/S3/VertexAlgebra/FactorialFockMetric.weight_pos`
