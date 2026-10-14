# LatticeOscillatorFockMetric

## Abstract

Nondegeneracy and positive Gram metric of the native oscillator

The form is exactly LatticeOscillatorFockForm.fockForm on complex multivariate polynomials indexed by Fin D.rank times the natural numbers. Neither the original form nor either original oscillator mode is replaced. The left slot is conjugate-linear and the right slot is linear. Arbitrary finite superpositions and every frequency are included, without an occupation or energy cutoff.

Let H be a complex inverse Gram matrix, with H G = 1 and G H = 1. The left and right radicals of the constructed form vanish. The actual positive-mode adjoint makes the left radical stable under every Gram-weighted annihilator A_(i,r). Dividing by the nonzero frequency r+1 and summing with the corresponding row of H reconstructs the ordinary partial derivative. Strong induction on total polynomial degree therefore forces every derivative of a radical vector to vanish. In characteristic zero such a polynomial is constant. Its vacuum pairing is that constant, so the constant is zero. Hermitian symmetry then removes the right radical. Both original inverse equations remain explicit in the theorem statement; the reconstruction uses H G = 1. The proof also includes rank zero. This is algebraic separation, not surjectivity onto the full infinite algebraic dual.

For any real matrix F, coordinateSubstitution replaces X_(i,r) by the finite sum over j of F_ij X_(j,r). It preserves the constant coefficient and all frequencies. Composition corresponds to matrix multiplication in the order determined by row coordinates. Two inverse matrices give an actual algebra equivalence of the entire native polynomial carrier. A proved directional-derivative chain rule supplies the interaction with the unchanged original annihilators.

Suppose the real Gram matrix factors as F diag(d) F.transpose. No positivity is needed for this identity. In the transformed coordinates the form is diagonal on finite occupation monomials. The weight of occupation e is the product, over its finite support, of e_(i,r)! times ((r+1) d_i) raised to e_(i,r). Insertion of one oscillator multiplies this weight by (e_(i,r)+1)(r+1)d_i. This factorial recursion proves the creator-partial adjoint for the explicit diagonal coefficient pairing. The actual derivative chain rule and the Gram factorization identify its pullback with the original form by the previously proved uniqueness theorem. The coordinate isometry is thus proved, not assumed.

For a positive definite real Gram matrix, the existing real LDL decomposition supplies F and d. The diagonal entries d_i are strictly positive because the inverse lower-triangular coordinate change is invertible and preserves positive definiteness by congruence. The inverse coordinates give a Gram-orthogonal real oscillator basis. Two occupation monomials in this basis pair to zero unless their entire finite occupation functions agree. Equal occupations have exactly the factorial-frequency weight above. Equality of the whole occupation functions also accounts for unequal frequencies.

For an arbitrary polynomial p, the original self-pairing equals the real finite sum of transformed coefficient norm-squares multiplied by the positive factorial-frequency weights. The proved coordinate equivalence sends a nonzero p to a nonzero polynomial, so at least one coefficient is nonzero. Its summand is strictly positive and all summands are nonnegative. Consequently every nonzero native state has strictly positive self-pairing. The one-particle positive-definite premise is finite-dimensional; the all-state conclusion ranges over the full algebraic oscillator space.

A negative or indefinite integral Gram matrix may still have an inverse. Nondegeneracy does not imply positivity: already a single creation state has self-pairing (r+1) G_ii. Real coordinate changes are essential to the displayed Hermitian Gram identity. Arbitrary complex coordinates require a conjugate transpose instead of an ordinary transpose.

These are standard algebraic Fock metric results and their native-carrier formal bridge; no mathematical novelty is asserted. They do not supply a charged PCT operator, the full ghost pairing, adjointness of the original BRST differential, orthogonality of boundaries to cycles, a quotient metric, a real Lorentzian transverse-frame supplier, or an isometry with a physical cohomology quotient. Global no-ghost, Leech and moonshine realization, full string theory and AdS/CFT remain separate mathematical obligations.

**Definition 1.1 (Finite occupation factorial-frequency weight).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.occupationWeight`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.occupationWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is taken over the finite support of the occupation function, including arbitrary repeated occupations and arbitrary frequencies.

**Definition 1.2 (Actual polynomial coordinate equivalence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.coordinateEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse laws are proved from the two matrix inverse equations and the actual polynomial substitutions.

**Theorem 1.3 (Both radicals vanish).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derivative stability and degree descent establish separation on the complete native polynomial carrier under the original inverse Gram equations.

**Theorem 1.4 (Proved native Gram-coordinate pairing).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_coordinate_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_coordinate_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact transformed coefficient pairing follows from the factorial recursion and the actual annihilator chain rule. The real Gram factorization is its only metric premise.

**Theorem 1.5 (Exact occupation kernel in real orthogonal coordinates).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_orthogonal_monomials`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_orthogonal_monomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unequal occupation functions pair to zero; equal ones pair to the exact weighted factorial product.

**Theorem 1.6 (Finite transformed coefficient norm identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_norm_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_norm_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity uses the real LDL coordinates of the given one-particle Gram matrix and the coefficient support of the actual transformed polynomial.

**Theorem 1.7 (Strict positivity on every nonzero polynomial).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis is positive definiteness of the real one-particle Gram matrix. Strict positivity of the complete multiparticle form is the conclusion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.coordinateEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_coordinate_factorization`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_nondegenerate`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_norm_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_orthogonal_monomials`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.fockForm_positive`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockMetric.occupationWeight`
- Dependency: [D5/S3/VertexAlgebra/LatticeOscillatorFockForm](LatticeOscillatorFockForm.md)
