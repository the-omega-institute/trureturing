# Infinite joint Gaussian Fock vector

## Abstract

Actual infinite joint Gaussian coefficients from common finite principal blocks.

This module constructs the infinite-mode Gaussian Fock coefficients and vector. It does not establish the full field or scientific programme. The normalization is the classical factorial Bargmann/Fock normalization, with weight(d)=product_i d(i)! and scale(d)=sqrt(weight(d)). No literature novelty is claimed.

The input is a genuine bounded complex-linear one-particle operator L on l2(I). Its actual coordinate matrix K(i,j)=(L e_j)(i) is symmetric in the holomorphic sense K(i,j)=K(j,i), without conjugation. Assume 0<=q<1, norm(L)<=q, summability of the nonnegative pair-indexed series sum_(i,j) abs(K(i,j))^2, and its total <=M. No Gaussian coefficient, norm or summability certificate is a premise. The coefficient, common-block and scalar summability layers do not assume countability of I.

**Theorem 1.1 (Natural principal compression).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.compression_eq_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.compression_eq_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's orthogonal-family isometry gives the finite ON inclusion J_S from EuclideanSpace(S) into l2(I). Its adjoint is the coordinate projection P_S. The matrix of P_S L J_S is exactly K restricted to S x S. Contractivity of J_S and P_S yields the finite operator bound <=q. One finite product S x S embeds injectively in I x I, giving the finite HS mass <=M without exchanging two series.

**Theorem 1.2 (Projection of the actual quadratic).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.quadratic_projection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.quadratic_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any injective map e between finite variable types, killCompl sets every variable outside its image to zero. Applied to Q_K=(1/2) sum_(i,j) K(i,j) X_i X_j, the finite sums reduce to the principal quadratic Q_(K restricted along e). This preserves every cross term and uses no assumed coefficient consistency. This polynomial identity is consumed by gaussianPiece_projection.

**Theorem 1.3 (Exact stabilization with zero added occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.gaussianCoefficient_enlarge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.gaussianCoefficient_enlarge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projection is an algebra homomorphism, so it takes Q_K^n/n! to the actual restricted gaussianPiece at every n. Mathlib's coeff_killCompl identifies the coefficient of d with the coefficient of its zero extension. Degree is preserved. The proof covers the empty type and arbitrary repeated occupations, not just square-free monomials.

**Theorem 1.4 (Any containing block computes the same coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.coefficient_on_block`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.coefficient_on_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define g(d) in the finite block support(d). The proved enlargement identity shows that every finite S containing support(d) computes exactly the same native gaussianCoefficient. Thus independence of S is a theorem about actual polynomial coefficients. It is not stored in a data field or used as an assumption.

**Theorem 1.5 (One common block for a finite occupation family).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.finite_occupation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.finite_occupation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given an arbitrary finite family F of occupations, set S=union_(d in F) support(d). Restriction into this ONE S is injective on F, preserves each factorial weight and computes each g(d). Apply FactorialFockQuadraticEstimate.finite_occupation_bound once to the image family and K restricted to S. The compression bounds give sum_(d in F) weight(d)*abs(g(d))^2 <= exp(M/(2*(1-q^2))). No summand uses a separate analytic cutoff.

**Theorem 1.6 (The whole joint occupation sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.occupation_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.occupation_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative finite-subsum boundedness gives summability over the entire occupation type by Mathlib's real series criterion. Its total is bounded by the same exponential. No mode/particle sum is interchanged and no determinant or Takagi formula is required. The cofinal finite-subsum method is adapted from the completed OriginalFullColourSummability source candidate; its scalar Corr bridge is neither imported nor assumed here.

**Theorem 1.7 (The actual Gaussian Hilbert vector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.vector_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.vector_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For countable I, after proving summability, form the actual l2 element with coordinate scale(d)*g(d). Parseval identifies its squared norm with the full weighted occupation sum. Its vacuum coefficient is one, its odd-degree coefficients vanish, and for empty mode types it is exactly the vacuum unit vector. HilbertBasis.hasSum_repr supplies unconditional convergence of its ON expansion. A required future continuation is to construct the coefficient operator from this actual vector; no current consumer is asserted here.

Still external: identify the abstract K and its Gaussian polynomial with full native normal+Corr inputs, Gram whitening, positive-frequency damping and same-term exponent regrouping. Official checks, freeze and delivery remain pending; the faithful four-slot dependent-family audit remains unfinished under linked issues 24524 and 24498. The current owner has no valid registration: lawful realization/readout, source selection and reconstruction, variation, sensitivity and observational-dependence evidence remain missing. Inherited finite-supplier audit findings do not describe a current-owner registration.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.coefficient_on_block`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.compression_eq_matrix`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.finite_occupation_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.gaussianCoefficient_enlarge`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.occupation_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.quadratic_projection`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock.vector_norm_sq`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate](FactorialFockQuadraticEstimate.md)
