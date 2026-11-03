# Factorial Fock quadratic estimate

## Abstract

An operator-norm and Hilbert-Schmidt bound for all mixed Gaussian degrees in the existing factorial Fock metric.

The finite mode type may be empty. The complex matrix A is symmetric, with actual Euclidean operator norm at most q, where 0<=q<1. Set Q_A=(1/2)*sum_ij A_ij X_i X_j and G_n=Q_A^n/n!. The squared norm is the real self-pairing of the existing FactorialFockMetric Hilbert embedding. No Gaussian norm formula, assumed boundedness, Takagi decomposition, finite-degree restriction or summability premise is introduced.

**Definition 1.1 (Factorial squared norm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.mass`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass is the real part of the existing factorial Fock self-pairing.

**Definition 1.2 (Symmetric quadratic creation polynomial).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.quadratic`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.quadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite complex matrix A, Q_A is one half of the sum of A_ij X_i X_j over both indices.

**Definition 1.3 (Gaussian homogeneous pieces).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth piece is Q_A raised to n and divided by n factorial.

**Definition 1.4 (Occupation coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient at occupation d is selected from G_(degree(d)/2); the homogeneity theorem below handles odd degrees.

**Theorem 1.5 (Exact factorial metric).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.mass_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.mass_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual squared Fock norm is sum_d weight(d)*|coeff(p,d)|^2. This equality is derived from the existing all-polynomial factorial pairing.

**Theorem 1.6 (CCR creation estimate in every degree).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.quadratic_creation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.quadratic_creation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every polynomial p, sum_i mass((sum_j A_ij X_j)*p) <= HS(A)^2*mass(p)+q^2*sum_j mass(partial_j p). The proof first derives the exact creation/derivative commutator identity, with conjugated coefficients on the derivative vector. The scalar Euclidean matrix norm bound is then applied at each occupation and summed with its factorial weight.

**Theorem 1.7 (Exact particle-number identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gradient_mass`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gradient_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For homogeneous p of degree k, sum_i mass(partial_i p)=k*mass(p), using Mathlib Euler identity and the existing creation/pderiv adjoint law.

**Theorem 1.8 (Exact Gaussian annihilation equation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece_pderiv`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece_pderiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetry gives partial_i G_(n+1)=(sum_j A_ij X_j)*G_n. The factor 1/2 and n! are explicitly derived and retained.

**Theorem 1.9 (All-degree Gaussian recurrence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.degree_mass_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.degree_mass_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a_n=mass(G_n), (n+1)*a_(n+1) <= (HS(A)^2/2+q^2*n)*a_n. This is a bound for every particle number, including all mixed and repeated occupations.

**Theorem 1.10 (Uniform dimension and particle bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.all_degree_partial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.all_degree_partial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sum of a_n through N is bounded by exp(HS(A)^2/(2*(1-q^2))). The analytic recurrence theorem supplies the same constant for every N.

**Theorem 1.11 (Infinite Gaussian degree sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.all_degree_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.all_degree_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete sequence of polynomial Gaussian square masses is summable; the result is not limited to a finite degree.

**Theorem 1.12 (Vacuum normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero occupation has coefficient one, including when the finite mode type is empty.

**Theorem 1.13 (Odd occupations vanish).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_odd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the total occupation degree is odd, homogeneity forces its Gaussian coefficient to vanish.

**Theorem 1.14 (Even degree selection).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_even`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An occupation of total degree 2n has Gaussian coefficient exactly its coefficient in G_n.

**Theorem 1.15 (Mixed coefficient equation with multiplicities).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece_coefficient_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece_coefficient_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient extraction from the annihilation equation gives (d_i+1)*coeff(G_(n+1),d+e_i)=sum_j A_ij*coeff(X_j*G_n,d). This is the exact equation needed for the still-missing labelled Wick comparison, with factorial multiplicities intact.

**Theorem 1.16 (Arbitrary mixed occupation subsets).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.finite_occupation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.finite_occupation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For g_A(d)=coeff(G_(degree(d)/2),d), every finite occupation subset S satisfies sum_(d in S) weight(d)*|g_A(d)|^2 <= exp(HS(A)^2/(2*(1-q^2))). The proof bounds S inside a finite degree rectangle, with a constant independent of that rectangle. Vacuum equals one and odd occupations vanish.

**Theorem 1.17 (True factorial sum over infinitely many occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.occupation_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.occupation_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the finite matrix A, the infinite mixed occupation coefficient sequence has summable weight(d)*|g_A(d)|^2. No desired source value is defined to equal g_A.

Identifying an actual Corr/Wick source with weight(d)*g_A(d), stabilizing coefficients under finite-mode transport, passing over infinitely many modes, and constructing an actual source representer are separate mathematical obligations. The present results concern the finite-matrix analytic supplier. The determinant norm identity, including the intended -1/2 exponent for A* A, remains open here; no identification with gaussianDet(z) is proved.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.all_degree_partial_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.all_degree_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.degree_mass_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.finite_occupation_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_even`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_odd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianCoefficient_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece_coefficient_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gaussianPiece_pderiv`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.gradient_mass`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.mass`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.mass_eq_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.occupation_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.quadratic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.quadratic_creation_bound`
- Dependency: [D5/S3/VertexAlgebra/FactorialFockMetric](../FactorialFockMetric.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant](GaussianDegreeMajorant.md)
