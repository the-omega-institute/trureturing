# Original Current Positive Oscillator Metric

## Abstract

Original Current Positive Oscillator Metric

Let D be the original LatticeData, with integral Gram matrix G and oscillator polynomial algebra Oscillator D. The sole metric assumption is hpos : (gramReal D).PosDef. Real spectral decomposition constructs S with S transpose times S equal to G, together with an explicit two-sided inverse. Multiplying S by the square root of k+1/2 at each natural mode gives a colour substitution and its inverse on the same polynomial algebra.

Pulling the factorial Fock form back along this algebra equivalence gives an InnerProductSpace.Core. The derived Gram law identifies the transformed positive current on generators; polynomial induction and Leibniz extend the identity to all states. The factorial creation/derivative pairing and Hermitian symmetry then give the original current formal adjoint at every integer j, with the mode reversed to -j-1. The form is conjugate linear first and linear second. All off-diagonal entries of G and rank zero are included.

Mathlib supplies the real Hermitian spectral theorem (Alexander Bentkamp and contributors, Apache 2.0), matrix identities, polynomial algebra, derivations and inner-product laws. The original half-mode architecture is due to Kalle Kytölä (2025), the additional actual half-integer implementation (2026), VirasoroProject and DN/BK/FLM; the corresponding operator sources carry their notices and licenses. Classical real spectral Gram/Bargmann Fock normalization carries no novelty claim. The factorial form and its creation/derivative pairing are those of FactorialFockMetric.

Second-slot additivity and scalar linearity follow by unfolding oscillatorInner and the factorial inner, then applying map_add/map_smul and inner_add_right/inner_smul_right. Strict positivity follows from re_inner_self_pos and injectivity of the factorial embedding composed with U.

For one-particle vectors, expand U(X(i,k)) and U(X(l,m)), distribute the finite sums, apply the factorial creation/derivative law and the vacuum monomial calculation, and use forward_gram. The result is zero when k differs from m and ((k:Complex)+1/2)*G(i,l) at equal modes, in the original colour order.

At rank zero, MvPolynomial.eq_C_of_isEmpty reduces every polynomial to its constant coefficient, which U.commutes fixes. The Core is still defined on that scalar polynomial algebra; current formulas indexed by Fin 0 have an empty colour telescope.

The pairing is an algebraic polynomial-domain identity. It does not assert physical/PCT or charged/ground unitarity, a maximal closed adjoint, bounded transport to the coefficient Hilbert space, or tensor, normal-sum and L0 identities. The frequency is the original half-integer j+1/2; the separate integer-neutral current is outside this statement.

**Definition 1.1 (gramReal).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.gramReal`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.gramReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real Gram matrix is the entrywise real cast of the original integral G. Declaration: abbrev gramReal (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ.

**Definition 1.2 (eigenvalue).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.eigenvalue`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.eigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Eigenvalues are those of Mathlib’s Hermitian structure derived from positive definiteness. Declaration: def eigenvalue (D : LatticeData) (hpos : (gramReal D).PosDef) : Fin D.rank → ℝ.

**Definition 1.3 (Q).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real eigenvector unitary is read from the same Hermitian spectral data. Declaration: def Q (D : LatticeData) (hpos : (gramReal D).PosDef) :     Matrix (Fin D.rank) (Fin D.rank) ℝ.

**Definition 1.4 (rootDiagonal).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal contains the real square roots of the positive eigenvalues. Declaration: def rootDiagonal (D : LatticeData) (hpos : (gramReal D).PosDef) :     Matrix (Fin D.rank) (Fin D.rank) ℝ.

**Definition 1.5 (inverseRootDiagonal).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverseRootDiagonal`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverseRootDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse diagonal uses inverses of those square roots; nonzeroness is proved. Declaration: def inverseRootDiagonal (D : LatticeData) (hpos : (gramReal D).PosDef) :     Matrix (Fin D.rank) (Fin D.rank) ℝ.

**Definition 1.6 (S).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.S`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

New-colour rows and original-colour columns are obtained as rootDiagonal times Q transpose. Declaration: def S (D : LatticeData) (hpos : (gramReal D).PosDef) :     Matrix (Fin D.rank) (Fin D.rank) ℝ.

**Definition 1.7 (R).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.R`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit inverse is Q times inverseRootDiagonal. Declaration: def R (D : LatticeData) (hpos : (gramReal D).PosDef) :     Matrix (Fin D.rank) (Fin D.rank) ℝ.

**Theorem 1.8 (eigenvalue pos).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.eigenvalue_pos`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.eigenvalue_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib Matrix.PosDef.eigenvalues_pos supplies strict positivity for the square-root arguments. Declaration: theorem eigenvalue_pos (D : LatticeData) (hpos : (gramReal D).PosDef)     (a : Fin D.rank) : 0 < eigenvalue D hpos a.

**Theorem 1.9 (root eigenvalue ne zero).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.root_eigenvalue_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.root_eigenvalue_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real.sqrt_pos and strict eigenvalue positivity discharge the diagonal inverse denominators. Declaration: theorem root_eigenvalue_ne_zero (D : LatticeData) (hpos : (gramReal D).PosDef)     (a : Fin D.rank) : Real.sqrt (eigenvalue D hpos a) ≠ 0.

**Theorem 1.10 (Q transpose mul).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q_transpose_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q_transpose_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unitary.coe_star_mul_self over the real matrix gives the first orthogonality direction. Declaration: theorem Q_transpose_mul (D : LatticeData) (hpos : (gramReal D).PosDef) :     (Q D hpos)ᵀ * Q D hpos = 1.

**Theorem 1.11 (Q mul transpose).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q_mul_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q_mul_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unitary.coe_mul_star_self gives the second orthogonality direction. Declaration: theorem Q_mul_transpose (D : LatticeData) (hpos : (gramReal D).PosDef) :     Q D hpos * (Q D hpos)ᵀ = 1.

**Theorem 1.12 (spectral factorization).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.spectral_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.spectral_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib’s Hermitian spectral theorem reconstructs the original Gram matrix from Q and its eigenvalues. Declaration: theorem spectral_factorization (D : LatticeData) (hpos : (gramReal D).PosDef) :     Q D hpos * Matrix.diagonal (eigenvalue D hpos) * (Q D hpos)ᵀ =       gramReal D.

**Theorem 1.13 (rootDiagonal square).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix.diagonal_mul_diagonal and Real.mul_self_sqrt compute the square. Declaration: theorem rootDiagonal_square (D : LatticeData) (hpos : (gramReal D).PosDef) :     rootDiagonal D hpos * rootDiagonal D hpos =       Matrix.diagonal (eigenvalue D hpos).

**Theorem 1.14 (rootDiagonal inverse).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise mul_inv_cancel₀ gives the first diagonal inverse law. Declaration: theorem rootDiagonal_inverse (D : LatticeData) (hpos : (gramReal D).PosDef) :     rootDiagonal D hpos * inverseRootDiagonal D hpos = 1.

**Theorem 1.15 (inverse rootDiagonal).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverse_rootDiagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverse_rootDiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise inv_mul_cancel₀ gives the reverse diagonal inverse law. Declaration: theorem inverse_rootDiagonal (D : LatticeData) (hpos : (gramReal D).PosDef) :     inverseRootDiagonal D hpos * rootDiagonal D hpos = 1.

**Theorem 1.16 (S transpose mul).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.S_transpose_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.S_transpose_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The required covariance orientation S transpose times S equals G is derived by the spectral theorem. Declaration: theorem S_transpose_mul (D : LatticeData) (hpos : (gramReal D).PosDef) :     (S D hpos)ᵀ * S D hpos = gramReal D.

**Theorem 1.17 (S mul R).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.S_mul_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.S_mul_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward inverse law follows by orthogonality and the diagonal cancellation. Declaration: theorem S_mul_R (D : LatticeData) (hpos : (gramReal D).PosDef) :     S D hpos * R D hpos = 1.

**Theorem 1.18 (R mul S).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.R_mul_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.R_mul_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse inverse law follows by the opposite diagonal cancellation and orthogonality. Declaration: theorem R_mul_S (D : LatticeData) (hpos : (gramReal D).PosDef) :     R D hpos * S D hpos = 1.

**Definition 1.19 (SC).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real mixing matrix is mapped to Complex through Complex.ofRealHom. Declaration: def SC (D : LatticeData) (hpos : (gramReal D).PosDef) :     Matrix (Fin D.rank) (Fin D.rank) ℂ.

**Definition 1.20 (RC).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.RC`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.RC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit real inverse is mapped through the same complex ring homomorphism. Declaration: def RC (D : LatticeData) (hpos : (gramReal D).PosDef) :     Matrix (Fin D.rank) (Fin D.rank) ℂ.

**Theorem 1.21 (SC mul RC).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC_mul_RC`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC_mul_RC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping the already proved real forward inverse law gives complex cancellation. Declaration: theorem SC_mul_RC (D : LatticeData) (hpos : (gramReal D).PosDef) :     SC D hpos * RC D hpos = 1.

**Theorem 1.22 (RC mul SC).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.RC_mul_SC`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.RC_mul_SC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping the reverse real law gives the reverse complex cancellation. Declaration: theorem RC_mul_SC (D : LatticeData) (hpos : (gramReal D).PosDef) :     RC D hpos * SC D hpos = 1.

**Theorem 1.23 (SC gram).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC_gram`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entrywise extraction of S transpose times S and exact casts retain every off-diagonal original G entry. Declaration: theorem SC_gram (D : LatticeData) (hpos : (gramReal D).PosDef)     (i l : Fin D.rank) :     (∑ a : Fin D.rank, SC D hpos a i * SC D hpos a l) = (D.G i l : ℂ).

**Definition 1.24 (modeReal).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeReal`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The physical positive half-mode is k plus one half in real scalars. Declaration: def modeReal (k : ℕ) : ℝ.

**Definition 1.25 (modeScale).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex scale is the real square root of the positive half-mode. Declaration: def modeScale (k : ℕ) : ℂ.

**Theorem 1.26 (modeReal pos).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeReal_pos`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeReal_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural k gives a strictly positive real half-mode. Declaration: theorem modeReal_pos (k : ℕ) : 0 < modeReal k.

**Theorem 1.27 (modeScale ne zero).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the real square root proves the complex scale is nonzero. Declaration: theorem modeScale_ne_zero (k : ℕ) : modeScale k ≠ 0.

**Theorem 1.28 (modeScale square).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square of the real-derived complex scale is k plus one half. Declaration: theorem modeScale_square (k : ℕ) : modeScale k * modeScale k = (k : ℂ) + 1 / 2.

**Definition 1.29 (forwardMatrix).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.forwardMatrix`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.forwardMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same-mode colour matrix has entries modeScale(k) times SC(a,i). Declaration: def forwardMatrix (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :     Matrix (Fin D.rank) (Fin D.rank) ℂ.

**Definition 1.30 (inverseMatrix).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverseMatrix`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse has original-colour row i, new-colour column a, inverse scale and RC(i,a). Declaration: def inverseMatrix (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :     Matrix (Fin D.rank) (Fin D.rank) ℂ.

**Theorem 1.31 (forward inverse).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.forward_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.forward_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite matrix multiplication separates the scale cancellation from SC times RC. Declaration: theorem forward_inverse (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :     forwardMatrix D hpos k * inverseMatrix D hpos k = 1.

**Theorem 1.32 (inverse forward).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverse_forward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverse_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse finite matrix product separates the inverse scale cancellation from RC times SC. Declaration: theorem inverse_forward (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :     inverseMatrix D hpos k * forwardMatrix D hpos k = 1.

**Definition 1.33 (variableImage).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.variableImage`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.variableImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite colour mixing stays at the same natural mode and in the same polynomial ring. Declaration: def variableImage (A : ℕ → Matrix n n ℂ) (x : n × ℕ) :     MvPolynomial (n × ℕ) ℂ. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Definition 1.34 (substitution).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib MvPolynomial.aeval extends the actual finite variable images as an algebra homomorphism. Declaration: def substitution (A : ℕ → Matrix n n ℂ) :     MvPolynomial (n × ℕ) ℂ →ₐ[ℂ] MvPolynomial (n × ℕ) ℂ. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.35 (substitution X).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib aeval_X computes a generator image for composition and U. Declaration: theorem substitution_X (A : ℕ → Matrix n n ℂ) (x : n × ℕ) :     substitution A (X x) = variableImage A x. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.36 (variableImage one).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.variableImage_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.variableImage_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity matrix gives the original generator by a finite delta sum. Declaration: theorem variableImage_one (x : n × ℕ) :     variableImage (fun _ => (1 : Matrix n n ℂ)) x = X x. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.37 (substitution variableImage).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_variableImage`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_variableImage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite sum interchange proves the exact matrix composition order before polynomial freeness is used. Declaration: theorem substitution_variableImage (A B : ℕ → Matrix n n ℂ) (x : n × ℕ) :     substitution A (variableImage B x) =       variableImage (fun k => A k * B k) x. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.38 (substitution comp).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_comp`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial algebra-homomorphism extensionality extends that generator computation to composition. Declaration: theorem substitution_comp (A B : ℕ → Matrix n n ℂ) :     (substitution A).comp (substitution B) =       substitution (fun k => A k * B k). Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.39 (substitution one).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial extensionality identifies identity-matrix substitution with AlgHom.id. Declaration: theorem substitution_one :     substitution (fun _ => (1 : Matrix n n ℂ)) =       AlgHom.id ℂ (MvPolynomial (n × ℕ) ℂ). Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.40 (substitution inverse).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic derived composition formula turns a matrix inverse law into homomorphism cancellation. Declaration: theorem substitution_inverse (A B : ℕ → Matrix n n ℂ)     (hAB : ∀ k, A k * B k = 1) :     (substitution A).comp (substitution B) =       AlgHom.id ℂ (MvPolynomial (n × ℕ) ℂ). Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Definition 1.41 (substitutionEquiv).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitutionEquiv`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitutionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AlgEquiv.ofAlgHom packages the two generic inverse homomorphisms. Only this generic construction has inverse hypotheses. Declaration: def substitutionEquiv (A B : ℕ → Matrix n n ℂ)     (hAB : ∀ k, A k * B k = 1) (hBA : ∀ k, B k * A k = 1) :     MvPolynomial (n × ℕ) ℂ ≃ₐ[ℂ] MvPolynomial (n × ℕ) ℂ. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Definition 1.42 (lowering).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite weighted sum of Mathlib partial derivations defines the actual polynomial lowering derivation. Declaration: def lowering (A : ℕ → Matrix n n ℂ) (i : n) (k : ℕ) :     Derivation ℂ (MvPolynomial (n × ℕ) ℂ) (MvPolynomial (n × ℕ) ℂ). Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.43 (lowering apply).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derivation.coeFnAddMonoidHom and finite-sum linearity expose the exact weighted derivative. Declaration: theorem lowering_apply (A : ℕ → Matrix n n ℂ) (i : n) (k : ℕ)     (p : MvPolynomial (n × ℕ) ℂ) :     lowering A i k p = ∑ a : n, A k a i • MvPolynomial.pderiv (a, k) p. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.44 (lowering X).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partial derivative delta law evaluates lowering on every colour and mode generator. Declaration: theorem lowering_X (A : ℕ → Matrix n n ℂ) (i l : n) (k m : ℕ) :     lowering A i k (X (l, m)) =       if k = m then A k l i • (1 : MvPolynomial (n × ℕ) ℂ) else 0. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Theorem 1.45 (lowering variableImage).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_variableImage`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_variableImage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The resulting generator pairing is the finite column Gram sum when the modes agree, and zero otherwise. Declaration: theorem lowering_variableImage (A : ℕ → Matrix n n ℂ)     (i l : n) (k m : ℕ) :     lowering A i k (variableImage A (l, m)) =       if k = m then (∑ a : n, A k a i * A k a l) •         (1 : MvPolynomial (n × ℕ) ℂ) else 0. Section context: universe u; variable {n : Type u} [Fintype n] [DecidableEq n].

**Definition 1.46 (U).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.U`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward algebra equivalence is on the exact original Oscillator D; the two inverse hypotheses are discharged by proved Gram identities. Declaration: def U (D : LatticeData) (hpos : (gramReal D).PosDef) :     Oscillator D ≃ₐ[ℂ] Oscillator D.

**Theorem 1.47 (U X).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.U_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.U_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original generator is sent to the explicit finite same-mode sum with original-colour column i. Declaration: theorem U_X (D : LatticeData) (hpos : (gramReal D).PosDef)     (i : Fin D.rank) (k : ℕ) :     U D hpos (X (i, k)) =       ∑ a : Fin D.rank, (modeScale k * (S D hpos a i : ℂ)) • X (a, k).

**Theorem 1.48 (conj forwardMatrix).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.conj_forwardMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.conj_forwardMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All mixing coefficients are complex images of real scalars, so conjugation fixes them. Declaration: theorem conj_forwardMatrix (D : LatticeData) (hpos : (gramReal D).PosDef)     (k : ℕ) (a i : Fin D.rank) :     conj (forwardMatrix D hpos k a i) = forwardMatrix D hpos k a i.

**Theorem 1.49 (forward gram).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.forward_gram`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.forward_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite forward coefficient Gram sum is frequency(k) times the original G(i,l). This is a conclusion, not a premise. Declaration: theorem forward_gram (D : LatticeData) (hpos : (gramReal D).PosDef)     (k : ℕ) (i l : Fin D.rank) :     (∑ a : Fin D.rank, forwardMatrix D hpos k a i * forwardMatrix D hpos k a l) =       frequency (k : ℤ) * (D.G i l : ℂ).

**Definition 1.50 (positiveDerivation).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original Gram annihilation derivation is multiplied by the physical half-mode frequency. Declaration: def positiveDerivation (D : LatticeData) (i : Fin D.rank) (k : ℕ) :     Derivation ℂ (Oscillator D) (Oscillator D).

**Theorem 1.51 (positiveDerivation current).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original nonnegative current definition is exactly this derivation on arbitrary polynomials. Declaration: theorem positiveDerivation_current (D : LatticeData) (i : Fin D.rank) (k : ℕ)     (p : Oscillator D) : positiveDerivation D i k p = current D i (k : ℤ) p.

**Theorem 1.52 (positiveDerivation X).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original annihilation generator law supplies frequency(k) times G(i,l) at equal modes. Declaration: theorem positiveDerivation_X (D : LatticeData) (i l : Fin D.rank) (k m : ℕ) :     positiveDerivation D i k (X (l, m)) =       if k = m then (frequency (k : ℤ) * (D.G i l : ℂ)) •         (1 : Oscillator D) else 0.

**Theorem 1.53 (lowering U X).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_U_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_U_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved forward Gram law gives the annihilation intertwiner on every original generator. Declaration: theorem lowering_U_X (D : LatticeData) (hpos : (gramReal D).PosDef)     (i l : Fin D.rank) (k m : ℕ) :     lowering (forwardMatrix D hpos) i k (U D hpos (X (l, m))) =       U D hpos (positiveDerivation D i k (X (l, m))).

**Theorem 1.54 (U positiveDerivation).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.U_positiveDerivation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.U_positiveDerivation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial induction with constants, addition and the actual Leibniz rule extends the intertwiner to every state. Declaration: theorem U_positiveDerivation (D : LatticeData) (hpos : (gramReal D).PosDef)     (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :     U D hpos (positiveDerivation D i k p) =       lowering (forwardMatrix D hpos) i k (U D hpos p).

**Definition 1.55 (oscillatorInner).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pull back the complete factorial form through U; this does not use the unweighted coefficient metric. Declaration: def oscillatorInner (D : LatticeData) (hpos : (gramReal D).PosDef)     (p q : Oscillator D) : ℂ.

**Theorem 1.56 (oscillatorInner conj swap).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_conj_swap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_conj_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib inner_conj_symm on actual embedded U-images gives Hermitian symmetry. Declaration: theorem oscillatorInner_conj_swap (D : LatticeData) (hpos : (gramReal D).PosDef)     (p q : Oscillator D) : conj (oscillatorInner D hpos q p) =       oscillatorInner D hpos p q.

**Theorem 1.57 (oscillatorInner add first).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_add_first`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_add_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Linearity of U and factorial additivity supply the Core additivity field. Declaration: theorem oscillatorInner_add_first (D : LatticeData) (hpos : (gramReal D).PosDef)     (p q r : Oscillator D) : oscillatorInner D hpos (p + q) r =       oscillatorInner D hpos p r + oscillatorInner D hpos q r.

**Theorem 1.58 (oscillatorInner smul first).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_smul_first`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_smul_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Linearity of both embeddings and root inner_smul_left give conjugate first-slot scalar multiplication. Declaration: theorem oscillatorInner_smul_first (D : LatticeData) (hpos : (gramReal D).PosDef)     (c : ℂ) (p q : Oscillator D) : oscillatorInner D hpos (c • p) q =       conj c * oscillatorInner D hpos p q.

**Definition 1.59 (oscillatorCore).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorCore`

*Formalization.* `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact original oscillator carrier gets an InnerProductSpace.Core. Nonnegativity and definiteness use the factorial Core and U injectivity; no desired positivity is assumed. Declaration: def oscillatorCore (D : LatticeData) (hpos : (gramReal D).PosDef) :     InnerProductSpace.Core ℂ (Oscillator D).

**Theorem 1.60 (factorial variable lowering pairing).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.factorial_variable_lowering_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.factorial_variable_lowering_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distribute the finite creation and derivative sums, apply Mathlib sesquilinearity, and use the factorial all-polynomial pairing. Declaration: theorem factorial_variable_lowering_pairing (D : LatticeData)     (hpos : (gramReal D).PosDef) (i : Fin D.rank) (k : ℕ)     (p q : Oscillator D) :     D5.S3.VertexAlgebra.FactorialFockMetric.inner         (variableImage (forwardMatrix D hpos) (i, k) * p) q =       D5.S3.VertexAlgebra.FactorialFockMetric.inner p         (lowering (forwardMatrix D hpos) i k q).

**Theorem 1.61 (oscillator negative positive pairing).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_negative_positive_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_negative_positive_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the actual original negative multiplication current through U and pair it with the original positive derivation on arbitrary states. Declaration: theorem oscillator_negative_positive_pairing (D : LatticeData)     (hpos : (gramReal D).PosDef) (i : Fin D.rank) (k : ℕ)     (p q : Oscillator D) :     oscillatorInner D hpos (current D i (-(k : ℤ) - 1) p) q =       oscillatorInner D hpos p (current D i (k : ℤ) q).

**Theorem 1.62 (oscillator positive negative pairing).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_positive_negative_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_positive_negative_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hermitian symmetry reverses the proved original negative/positive pairing with the correct scalar convention. Declaration: theorem oscillator_positive_negative_pairing (D : LatticeData)     (hpos : (gramReal D).PosDef) (i : Fin D.rank) (k : ℕ)     (p q : Oscillator D) :     oscillatorInner D hpos (current D i (k : ℤ) p) q =       oscillatorInner D hpos p (current D i (-(k : ℤ) - 1) q).

**Theorem 1.63 (oscillator current pairing).**

Lean statement: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_current_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_current_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D, positive Gram hpos, original colour i, integer mode j and arbitrary p,q, the formal algebraic adjoint is the original current at -j-1. Integer sign cases use the two half-mode laws; no desired pairing is an input. Declaration: theorem oscillator_current_pairing (D : LatticeData) (hpos : (gramReal D).PosDef)     (i : Fin D.rank) (j : ℤ) (p q : Oscillator D) :     (oscillatorCore D hpos).inner (current D i j p) q =       (oscillatorCore D hpos).inner p (current D i (-j - 1) q).

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q_mul_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.Q_transpose_mul`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.R`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.RC`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.RC_mul_SC`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.R_mul_S`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.S`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC_gram`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.SC_mul_RC`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.S_mul_R`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.S_transpose_mul`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.U`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.U_X`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.U_positiveDerivation`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.conj_forwardMatrix`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.eigenvalue`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.eigenvalue_pos`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.factorial_variable_lowering_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.forwardMatrix`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.forward_gram`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.forward_inverse`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.gramReal`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverseMatrix`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverseRootDiagonal`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverse_forward`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.inverse_rootDiagonal`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_U_X`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_X`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_apply`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.lowering_variableImage`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeReal`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeReal_pos`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.modeScale_square`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorCore`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_add_first`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_conj_swap`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillatorInner_smul_first`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_current_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_negative_positive_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.oscillator_positive_negative_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation_X`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.positiveDerivation_current`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal_inverse`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.rootDiagonal_square`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.root_eigenvalue_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.spectral_factorization`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitutionEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_X`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_comp`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_inverse`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_one`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.substitution_variableImage`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.variableImage`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalCurrentMetric.variableImage_one`
- Dependency: [D5/S3/VertexAlgebra/FactorialFockMetric](FactorialFockMetric.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormal](LatticeHalfFockCurrentNormal.md)
