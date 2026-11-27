# Fixed Weight-Two States from an Invariant Quadratic Projector

## Abstract

A nonzero proper Gram-orthogonal projector commuting with a family of charge isometries gives two linearly independent fixed weight-two states on the actual lattice carrier.

Let D be even integral LatticeData and G = gramComplex(D). All matrices are complex square matrices indexed by Fin(D.rank). For such a matrix A, conformalPolynomial(D,A) is one half of the sum over i and j of A(i,j) times X(i,0)X(j,0). The state omega(D,A) places that polynomial in charge zero on the actual finite-support carrier. Here transpose is the ordinary matrix transpose for the complex bilinear Gram form.

**Theorem 1.1 (Quadratic states determine symmetric matrices).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_injective_of_isSymm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_injective_of_isSymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A and B are symmetric and omega(D,A) = omega(D,B), then A = B. Read the charge-zero component, differentiate in X(i,0) and X(j,0), and take the constant coefficient. Symmetry cancels the factor one half against the two differentiated terms, recovering the matrix entry even when i = j.

**Theorem 1.2 (Oscillator substitution acts by matrix congruence).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.conformalPolynomial_substitution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.conformalPolynomial_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a complex algebra endomorphism of the oscillator algebra. Suppose it sends X(i,0) to the sum over k of M(k,i) times X(k,0) for each i. Expanding the quadratic with those substituted variables gives S(conformalPolynomial(D,A)) = conformalPolynomial(D,M A Mᵀ) for arbitrary A and M. The action on higher oscillator variables is unrestricted.

**Theorem 1.3 (Covariance under a vacuum-preserving neutral substitution).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the same substitution law for S and M. Let U be a complex-linear endomorphism of the carrier which sends single(0,p) to z times single(0,S(p)) for a fixed complex scalar z and every oscillator polynomial p. Suppose U fixes the vacuum. Applying the law to p = 1 forces z = 1 because the vacuum is nonzero. The polynomial substitution then gives U(omega(D,A)) = omega(D,M A Mᵀ).

**Theorem 1.4 (Quadratic covariance for the actual charge lift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.lift_omega`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.lift_omega` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every additive charge equivalence g and every A, the actual lift(D,g) sends omega(D,A) to omega(D,M A Mᵀ), where column i of M is the complex coordinate vector of g applied to the ith unit charge. The lift fixes the vacuum and acts on charge zero by its oscillator substitution with the neutral phase, so the covariance theorem applies.

**Theorem 1.5 (Every neutral quadratic state belongs to grade two).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_mem_grade_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_mem_grade_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every A, omega(D,A) belongs to grade(D,2). Each summand is supported in charge zero and its two frequency-one oscillator factors contribute one unit of energy each, including when their indices coincide. The grade is closed under sums and complex scaling.

**Theorem 1.6 (A Gram-orthogonal projector gives two independent fixed states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.projector_fixed_weight_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.projector_fixed_weight_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let g be a family of additive charge equivalences indexed by an arbitrary type ι, each preserving the integral bilinear form. Write M(t) for the mixing matrix of g(t). Suppose H is symmetric with H G = 1. Suppose P² = P, P ≠ 0, P ≠ 1, Pᵀ G = G P, and M(t) P = P M(t) for every t. Then omega(D,H) and omega(D,P H) each belong to grade(D,2). Mode one of Y(D,omega(D,H)) acts on each by the complex scalar 2, and lift(D,g(t)) fixes each for all t. The ordered pair ![omega(D,P H), omega(D,H)] is linearly independent over ℂ.

The square-matrix inverse identity gives G H = 1. To see that P H is symmetric, transpose it to H Pᵀ and rewrite H Pᵀ = H (Pᵀ G) H = H (G P) H = P H. For M = M(t), preservation of the bilinear form gives Mᵀ G M = G, hence Mᵀ G = G M⁻¹. It follows that M H Mᵀ G = 1 and thus M H Mᵀ = H. Commutation with P gives M (P H) Mᵀ = P H, so congruence covariance fixes both states. Grade membership and actualL0_eigen_iff_grade give the eigenvalue 2. The theorem omega_modes identifies Sugawara index zero with mode one of the stated field.

Symmetric coefficient recovery shows omega(D,H) is nonzero. Its vanishing would give H = 0 and thus 1 = 0, forcing P = 0. If c times omega(D,H) equalled omega(D,P H), moving the scalar into the coefficient matrix and recovering the symmetric coefficients would give c H = P H. Right multiplication by G gives c times 1 = P. Idempotence then gives c P = P, so P ≠ 0 implies c = 1 and hence P = 1, a contradiction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.conformalPolynomial_substitution`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.lift_omega`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_injective_of_isSymm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.omega_mem_grade_two`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.projector_fixed_weight_two`
- Dependency: [D5/S3/VertexAlgebra/Lattice/IsometryLift](../IsometryLift.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../../LatticeActualLZeroGrading.md)
