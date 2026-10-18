/- GID: D5/S3/VertexAlgebra/OriginalCurrentMetric
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/OriginalCurrentMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef, mathlib/module/Mathlib.Algebra.MvPolynomial.PDeriv]
   utility: none
   digest: The derived Gram change of variables gives the original current formal adjoint on all polynomial states and integer modes. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
import D5.S3.VertexAlgebra.FactorialFockMetric
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Positive Gram coordinates and the original half-current pairing

For the integral Gram matrix G of LatticeData D, assume only
hpos : (OriginalGram.gramReal D).PosDef. Real spectral decomposition gives
SᵀS = G and an explicit two-sided inverse. Multiplication by the square root
of k + 1/2 gives an invertible colour change at each natural mode. Its
polynomial algebra equivalence U pulls back the factorial Fock form to the
original Oscillator D. The Leibniz rule extends the Gram identity from
variables to arbitrary polynomials, giving the original half-current formal
adjoint at every integer mode j with reversal -j-1.

Off-diagonal Gram entries and rank zero are included. The form is conjugate
linear in its first argument and linear in its second. Covariance, inverse
laws, positivity of the form and the current pairing are derived from hpos.
FactorialFockMetric supplies the factorial form and creation/derivative law.
The pairing is an algebraic polynomial-domain identity; physical/PCT or
charged/ground unitarity, maximal closed adjoints and bounded transport to
the coefficient Hilbert space are outside its scope.

This is the classical real spectral Gram/Bargmann Fock normalization,
without a novelty claim. Mathlib's spectral theorem is due to Alexander
Bentkamp and contributors (Apache 2.0). The original half-mode operator
architecture is due to Kalle Kytölä (2025), the additional actual half-integer
implementation (2026), VirasoroProject and DN/BK/FLM; their notices and
licenses remain in the corresponding operator sources.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open ComplexConjugate

namespace D5.S3.VertexAlgebra.OriginalGram
open LatticeGeneratingFieldLocality LatticeHalfFock

abbrev gramReal (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  D.G.map (Int.cast : ℤ → ℝ)

def eigenvalue (D : LatticeData) (hpos : (gramReal D).PosDef) : Fin D.rank → ℝ :=
  hpos.isHermitian.eigenvalues

def Q (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  hpos.isHermitian.eigenvectorUnitary

def rootDiagonal (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  Matrix.diagonal fun a => Real.sqrt (eigenvalue D hpos a)

def inverseRootDiagonal (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  Matrix.diagonal fun a => (Real.sqrt (eigenvalue D hpos a))⁻¹

/-- Rows are the new colours, columns the ORIGINAL colours. -/
def S (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  rootDiagonal D hpos * (Q D hpos)ᵀ

/-- The inverse matrix Q times the inverse square-root diagonal. -/
def R (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  Q D hpos * inverseRootDiagonal D hpos

theorem eigenvalue_pos (D : LatticeData) (hpos : (gramReal D).PosDef)
    (a : Fin D.rank) : 0 < eigenvalue D hpos a :=
  hpos.eigenvalues_pos a

theorem root_eigenvalue_ne_zero (D : LatticeData) (hpos : (gramReal D).PosDef)
    (a : Fin D.rank) : Real.sqrt (eigenvalue D hpos a) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (eigenvalue_pos D hpos a))

theorem Q_transpose_mul (D : LatticeData) (hpos : (gramReal D).PosDef) :
    (Q D hpos)ᵀ * Q D hpos = 1 := by
  simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self hpos.isHermitian.eigenvectorUnitary

theorem Q_mul_transpose (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Q D hpos * (Q D hpos)ᵀ = 1 := by
  simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_mul_star_self hpos.isHermitian.eigenvectorUnitary

theorem spectral_factorization (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Q D hpos * Matrix.diagonal (eigenvalue D hpos) * (Q D hpos)ᵀ =
      gramReal D := by
  simpa [Q, eigenvalue, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hpos.isHermitian.spectral_theorem.symm

theorem rootDiagonal_square (D : LatticeData) (hpos : (gramReal D).PosDef) :
    rootDiagonal D hpos * rootDiagonal D hpos =
      Matrix.diagonal (eigenvalue D hpos) := by
  rw [rootDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact Real.mul_self_sqrt (eigenvalue_pos D hpos a).le

theorem rootDiagonal_inverse (D : LatticeData) (hpos : (gramReal D).PosDef) :
    rootDiagonal D hpos * inverseRootDiagonal D hpos = 1 := by
  have hd : (fun a => Real.sqrt (eigenvalue D hpos a) *
      (Real.sqrt (eigenvalue D hpos a))⁻¹) = fun _ => (1 : ℝ) := by
    funext a
    exact mul_inv_cancel₀ (root_eigenvalue_ne_zero D hpos a)
  rw [rootDiagonal, inverseRootDiagonal, Matrix.diagonal_mul_diagonal]
  rw [hd, Matrix.diagonal_one]

theorem inverse_rootDiagonal (D : LatticeData) (hpos : (gramReal D).PosDef) :
    inverseRootDiagonal D hpos * rootDiagonal D hpos = 1 := by
  have hd : (fun a => (Real.sqrt (eigenvalue D hpos a))⁻¹ *
      Real.sqrt (eigenvalue D hpos a)) = fun _ => (1 : ℝ) := by
    funext a
    exact inv_mul_cancel₀ (root_eigenvalue_ne_zero D hpos a)
  rw [inverseRootDiagonal, rootDiagonal, Matrix.diagonal_mul_diagonal]
  rw [hd, Matrix.diagonal_one]

/-- The required orientation Sᵀ S = G is a conclusion from hpos. -/
theorem S_transpose_mul (D : LatticeData) (hpos : (gramReal D).PosDef) :
    (S D hpos)ᵀ * S D hpos = gramReal D := by
  rw [S, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hdiag : (rootDiagonal D hpos)ᵀ = rootDiagonal D hpos := Matrix.diagonal_transpose _
  rw [hdiag]
  change (Q D hpos * rootDiagonal D hpos) *
      (rootDiagonal D hpos * (Q D hpos)ᵀ) = _
  calc
    _ = Q D hpos * (rootDiagonal D hpos * rootDiagonal D hpos) *
        (Q D hpos)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [rootDiagonal_square, spectral_factorization]

theorem S_mul_R (D : LatticeData) (hpos : (gramReal D).PosDef) :
    S D hpos * R D hpos = 1 := by
  calc
    _ = rootDiagonal D hpos * ((Q D hpos)ᵀ * Q D hpos) *
        inverseRootDiagonal D hpos := by simp only [S, R, Matrix.mul_assoc]
    _ = 1 := by rw [Q_transpose_mul, Matrix.mul_one, rootDiagonal_inverse]

theorem R_mul_S (D : LatticeData) (hpos : (gramReal D).PosDef) :
    R D hpos * S D hpos = 1 := by
  calc
    _ = Q D hpos * (inverseRootDiagonal D hpos * rootDiagonal D hpos) *
        (Q D hpos)ᵀ := by simp only [S, R, Matrix.mul_assoc]
    _ = 1 := by rw [inverse_rootDiagonal, Matrix.mul_one, Q_mul_transpose]

def SC (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ := (S D hpos).map Complex.ofRealHom

def RC (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ := (R D hpos).map Complex.ofRealHom

theorem SC_mul_RC (D : LatticeData) (hpos : (gramReal D).PosDef) :
    SC D hpos * RC D hpos = 1 := by
  simpa [SC, RC, ← Matrix.map_mul] using
    congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℝ =>
      M.map Complex.ofRealHom) (S_mul_R D hpos)

theorem RC_mul_SC (D : LatticeData) (hpos : (gramReal D).PosDef) :
    RC D hpos * SC D hpos = 1 := by
  simpa [SC, RC, ← Matrix.map_mul] using
    congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℝ =>
      M.map Complex.ofRealHom) (R_mul_S D hpos)

theorem SC_gram (D : LatticeData) (hpos : (gramReal D).PosDef)
    (i l : Fin D.rank) :
    (∑ a : Fin D.rank, SC D hpos a i * SC D hpos a l) = (D.G i l : ℂ) := by
  have h := congrFun (congrFun (S_transpose_mul D hpos) i) l
  change (∑ a : Fin D.rank, S D hpos a i * S D hpos a l) = (D.G i l : ℝ) at h
  change (∑ a : Fin D.rank, (S D hpos a i : ℂ) * (S D hpos a l : ℂ)) = _
  exact_mod_cast h

/-- The physical positive half-mode, in REAL scalars before any complex cast. -/
def modeReal (k : ℕ) : ℝ := (k : ℝ) + 1 / 2

def modeScale (k : ℕ) : ℂ := (Real.sqrt (modeReal k) : ℂ)

theorem modeReal_pos (k : ℕ) : 0 < modeReal k := by
  dsimp [modeReal]
  positivity

theorem modeScale_ne_zero (k : ℕ) : modeScale k ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (modeReal_pos k)))

theorem modeScale_square (k : ℕ) : modeScale k * modeScale k = (k : ℂ) + 1 / 2 := by
  have h := Real.mul_self_sqrt (modeReal_pos k).le
  simpa [modeScale, modeReal] using congrArg (Complex.ofReal : ℝ → ℂ) h

def forwardMatrix (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ := fun a i => modeScale k * SC D hpos a i

def inverseMatrix (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ := fun i a => (modeScale k)⁻¹ * RC D hpos i a

theorem forward_inverse (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :
    forwardMatrix D hpos k * inverseMatrix D hpos k = 1 := by
  ext i l
  change (∑ a, (modeScale k * SC D hpos i a) *
    ((modeScale k)⁻¹ * RC D hpos a l)) = _
  calc
    _ = (modeScale k * (modeScale k)⁻¹) *
        (∑ a, SC D hpos i a * RC D hpos a l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [mul_inv_cancel₀ (modeScale_ne_zero k), one_mul]
      exact congrFun (congrFun (SC_mul_RC D hpos) i) l

theorem inverse_forward (D : LatticeData) (hpos : (gramReal D).PosDef) (k : ℕ) :
    inverseMatrix D hpos k * forwardMatrix D hpos k = 1 := by
  ext i l
  change (∑ a, ((modeScale k)⁻¹ * RC D hpos i a) *
    (modeScale k * SC D hpos a l)) = _
  calc
    _ = ((modeScale k)⁻¹ * modeScale k) *
        (∑ a, RC D hpos i a * SC D hpos a l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [inv_mul_cancel₀ (modeScale_ne_zero k), one_mul]
      exact congrFun (congrFun (RC_mul_SC D hpos) i) l

end D5.S3.VertexAlgebra.OriginalGram

namespace D5.S3.VertexAlgebra.OriginalCurrentMetric
open OriginalGram
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeActualAnnihilation
open MvPolynomial

section FiniteSubstitution
universe u
variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Finite colour mixing at the SAME mode, in the SAME polynomial ring. -/
def variableImage (A : ℕ → Matrix n n ℂ) (x : n × ℕ) :
    MvPolynomial (n × ℕ) ℂ := ∑ a : n, A x.2 a x.1 • X (a, x.2)

def substitution (A : ℕ → Matrix n n ℂ) :
    MvPolynomial (n × ℕ) ℂ →ₐ[ℂ] MvPolynomial (n × ℕ) ℂ :=
  MvPolynomial.aeval (variableImage A)

@[simp] theorem substitution_X (A : ℕ → Matrix n n ℂ) (x : n × ℕ) :
    substitution A (X x) = variableImage A x := MvPolynomial.aeval_X _ _

@[simp] theorem variableImage_one (x : n × ℕ) :
    variableImage (fun _ => (1 : Matrix n n ℂ)) x = X x := by
  classical
  simp [variableImage, Matrix.one_apply, ite_smul]

/-- Matrix composition is proved by finite sums, before using freeness. -/
theorem substitution_variableImage (A B : ℕ → Matrix n n ℂ) (x : n × ℕ) :
    substitution A (variableImage B x) =
      variableImage (fun k => A k * B k) x := by
  classical
  simp only [variableImage, map_sum, map_smul, substitution_X,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_smul]
  congr 1
  change (∑ b : n, B x.2 b x.1 * A x.2 a b) =
    ∑ b : n, A x.2 a b * B x.2 b x.1
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

theorem substitution_comp (A B : ℕ → Matrix n n ℂ) :
    (substitution A).comp (substitution B) =
      substitution (fun k => A k * B k) := by
  apply MvPolynomial.algHom_ext
  intro x
  change substitution A (substitution B (X x)) = _
  rw [substitution_X, substitution_variableImage, substitution_X]

theorem substitution_one :
    substitution (fun _ => (1 : Matrix n n ℂ)) =
      AlgHom.id ℂ (MvPolynomial (n × ℕ) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [substitution_X, variableImage_one, AlgHom.id_apply]

theorem substitution_inverse (A B : ℕ → Matrix n n ℂ)
    (hAB : ∀ k, A k * B k = 1) :
    (substitution A).comp (substitution B) =
      AlgHom.id ℂ (MvPolynomial (n × ℕ) ℂ) := by
  rw [substitution_comp]
  simp only [hAB]
  exact substitution_one

/-- This generic algebra lemma is instantiated below with DERIVED matrix laws.
Neither inverse law is a hypothesis of the original-current result. -/
def substitutionEquiv (A B : ℕ → Matrix n n ℂ)
    (hAB : ∀ k, A k * B k = 1) (hBA : ∀ k, B k * A k = 1) :
    MvPolynomial (n × ℕ) ℂ ≃ₐ[ℂ] MvPolynomial (n × ℕ) ℂ :=
  AlgEquiv.ofAlgHom (substitution A) (substitution B)
    (substitution_inverse A B hAB) (substitution_inverse B A hBA)

/-- A finite weighted sum of partial derivatives. -/
def lowering (A : ℕ → Matrix n n ℂ) (i : n) (k : ℕ) :
    Derivation ℂ (MvPolynomial (n × ℕ) ℂ) (MvPolynomial (n × ℕ) ℂ) :=
  ∑ a : n, A k a i • MvPolynomial.pderiv (a, k)

theorem lowering_apply (A : ℕ → Matrix n n ℂ) (i : n) (k : ℕ)
    (p : MvPolynomial (n × ℕ) ℂ) :
    lowering A i k p = ∑ a : n, A k a i • MvPolynomial.pderiv (a, k) p := by
  unfold lowering
  change (Derivation.coeFnAddMonoidHom (∑ a : n,
    A k a i • MvPolynomial.pderiv (a, k))) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply]

theorem lowering_X (A : ℕ → Matrix n n ℂ) (i l : n) (k m : ℕ) :
    lowering A i k (X (l, m)) =
      if k = m then A k l i • (1 : MvPolynomial (n × ℕ) ℂ) else 0 := by
  classical
  rw [lowering_apply]
  by_cases h : k = m
  · subst m
    simp [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq,
      ite_smul, smul_ite, eq_comm]
  · simp [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq,
      h, Ne.symm h]

theorem lowering_variableImage (A : ℕ → Matrix n n ℂ)
    (i l : n) (k m : ℕ) :
    lowering A i k (variableImage A (l, m)) =
      if k = m then (∑ a : n, A k a i * A k a l) •
        (1 : MvPolynomial (n × ℕ) ℂ) else 0 := by
  classical
  simp only [variableImage, map_sum, Derivation.map_smul, lowering_X]
  by_cases h : k = m
  · subst m
    simp only [if_true, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  · simp [h]

end FiniteSubstitution

/-- The forward polynomial equivalence on the ORIGINAL oscillator variables. -/
def U (D : LatticeData) (hpos : (gramReal D).PosDef) :
    Oscillator D ≃ₐ[ℂ] Oscillator D :=
  substitutionEquiv (forwardMatrix D hpos) (inverseMatrix D hpos)
    (forward_inverse D hpos) (inverse_forward D hpos)

@[simp] theorem U_X (D : LatticeData) (hpos : (gramReal D).PosDef)
    (i : Fin D.rank) (k : ℕ) :
    U D hpos (X (i, k)) =
      ∑ a : Fin D.rank, (modeScale k * (S D hpos a i : ℂ)) • X (a, k) := by
  exact substitution_X (forwardMatrix D hpos) (i, k)

@[simp] theorem conj_forwardMatrix (D : LatticeData) (hpos : (gramReal D).PosDef)
    (k : ℕ) (a i : Fin D.rank) :
    conj (forwardMatrix D hpos k a i) = forwardMatrix D hpos k a i := by
  simp [forwardMatrix, modeScale, SC]

theorem forward_gram (D : LatticeData) (hpos : (gramReal D).PosDef)
    (k : ℕ) (i l : Fin D.rank) :
    (∑ a : Fin D.rank, forwardMatrix D hpos k a i * forwardMatrix D hpos k a l) =
      frequency (k : ℤ) * (D.G i l : ℂ) := by
  calc
    _ = (modeScale k * modeScale k) *
        (∑ a : Fin D.rank, SC D hpos a i * SC D hpos a l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [forwardMatrix]
      ring
    _ = _ := by
      rw [modeScale_square, SC_gram]
      simp only [frequency, Int.cast_natCast]

def positiveDerivation (D : LatticeData) (i : Fin D.rank) (k : ℕ) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  frequency (k : ℤ) • annihilationDerivation D i k

theorem positiveDerivation_current (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p : Oscillator D) : positiveDerivation D i k p = current D i (k : ℤ) p := by
  simp [positiveDerivation, current, annihilation_apply,
    not_lt.mpr (Int.natCast_nonneg k)]

theorem positiveDerivation_X (D : LatticeData) (i l : Fin D.rank) (k m : ℕ) :
    positiveDerivation D i k (X (l, m)) =
      if k = m then (frequency (k : ℤ) * (D.G i l : ℂ)) •
        (1 : Oscillator D) else 0 := by
  simp only [positiveDerivation, Derivation.coe_smul, Pi.smul_apply,
    annihilation_apply, annihilate_X]
  split_ifs <;> simp [smul_smul]

theorem lowering_U_X (D : LatticeData) (hpos : (gramReal D).PosDef)
    (i l : Fin D.rank) (k m : ℕ) :
    lowering (forwardMatrix D hpos) i k (U D hpos (X (l, m))) =
      U D hpos (positiveDerivation D i k (X (l, m))) := by
  rw [U_X]
  change lowering (forwardMatrix D hpos) i k
    (variableImage (forwardMatrix D hpos) (l, m)) = _
  rw [lowering_variableImage, positiveDerivation_X, forward_gram]
  split_ifs <;> simp

/-- All-polynomial annihilation intertwiner, by Leibniz and the derived Gram law. -/
theorem U_positiveDerivation (D : LatticeData) (hpos : (gramReal D).PosDef)
    (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :
    U D hpos (positiveDerivation D i k p) =
      lowering (forwardMatrix D hpos) i k (U D hpos p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.derivation_C, map_zero]
    rw [show U D hpos (C c) = C c from (U D hpos).commutes c,
      MvPolynomial.derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    rcases x with ⟨l, m⟩
    rw [(positiveDerivation D i k).leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    rw [hp, ← lowering_U_X D hpos i l k m,
      (lowering (forwardMatrix D hpos) i k).leibniz]
    simp only [smul_eq_mul]

/-- The pullback of the factorial form along U. -/
def oscillatorInner (D : LatticeData) (hpos : (gramReal D).PosDef)
    (p q : Oscillator D) : ℂ :=
  D5.S3.VertexAlgebra.FactorialFockMetric.inner (U D hpos p) (U D hpos q)

theorem oscillatorInner_conj_swap (D : LatticeData) (hpos : (gramReal D).PosDef)
    (p q : Oscillator D) : conj (oscillatorInner D hpos q p) =
      oscillatorInner D hpos p q := by
  exact inner_conj_symm _ _

theorem oscillatorInner_add_first (D : LatticeData) (hpos : (gramReal D).PosDef)
    (p q r : Oscillator D) : oscillatorInner D hpos (p + q) r =
      oscillatorInner D hpos p r + oscillatorInner D hpos q r := by
  simp only [oscillatorInner, map_add, D5.S3.VertexAlgebra.FactorialFockMetric.inner_add_first]

theorem oscillatorInner_smul_first (D : LatticeData) (hpos : (gramReal D).PosDef)
    (c : ℂ) (p q : Oscillator D) : oscillatorInner D hpos (c • p) q =
      conj c * oscillatorInner D hpos p q := by
  simp only [oscillatorInner, D5.S3.VertexAlgebra.FactorialFockMetric.inner,
    map_smul, inner_smul_left]

def oscillatorCore (D : LatticeData) (hpos : (gramReal D).PosDef) :
    InnerProductSpace.Core ℂ (Oscillator D) where
  inner := oscillatorInner D hpos
  conj_inner_symm := oscillatorInner_conj_swap D hpos
  re_inner_nonneg p := (D5.S3.VertexAlgebra.FactorialFockMetric.core (Index D)).re_inner_nonneg _
  add_left := oscillatorInner_add_first D hpos
  smul_left p q c := oscillatorInner_smul_first D hpos c p q
  definite p hp := by
    apply (U D hpos).injective
    rw [map_zero]
    exact (D5.S3.VertexAlgebra.FactorialFockMetric.core (Index D)).definite (U D hpos p) hp

/-- Finite linear combinations of the factorial creation/derivative law,
using sesquilinearity and finite-sum additivity. -/
theorem factorial_variable_lowering_pairing (D : LatticeData)
    (hpos : (gramReal D).PosDef) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    D5.S3.VertexAlgebra.FactorialFockMetric.inner
        (variableImage (forwardMatrix D hpos) (i, k) * p) q =
      D5.S3.VertexAlgebra.FactorialFockMetric.inner p
        (lowering (forwardMatrix D hpos) i k q) := by
  classical
  have hsmulL (c : ℂ) (r s : Oscillator D) :
      D5.S3.VertexAlgebra.FactorialFockMetric.inner (c • r) s =
        conj c * D5.S3.VertexAlgebra.FactorialFockMetric.inner r s := by
    simp only [D5.S3.VertexAlgebra.FactorialFockMetric.inner, map_smul,
      inner_smul_left]
  have hsmulR (c : ℂ) (r s : Oscillator D) :
      D5.S3.VertexAlgebra.FactorialFockMetric.inner r (c • s) =
        c * D5.S3.VertexAlgebra.FactorialFockMetric.inner r s := by
    simp only [D5.S3.VertexAlgebra.FactorialFockMetric.inner, map_smul,
      inner_smul_right]
  have hsumL (f : Fin D.rank → Oscillator D) (r : Oscillator D) :
      D5.S3.VertexAlgebra.FactorialFockMetric.inner (∑ a, f a) r =
        ∑ a, D5.S3.VertexAlgebra.FactorialFockMetric.inner (f a) r := by
    simp only [D5.S3.VertexAlgebra.FactorialFockMetric.inner, map_sum, sum_inner]
  have hsumR (f : Fin D.rank → Oscillator D) (r : Oscillator D) :
      D5.S3.VertexAlgebra.FactorialFockMetric.inner r (∑ a, f a) =
        ∑ a, D5.S3.VertexAlgebra.FactorialFockMetric.inner r (f a) := by
    simp only [D5.S3.VertexAlgebra.FactorialFockMetric.inner, map_sum, inner_sum]
  rw [variableImage, Finset.sum_mul, lowering_apply, hsumL, hsumR]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_mul_assoc, hsmulL, hsmulR, conj_forwardMatrix,
    D5.S3.VertexAlgebra.FactorialFockMetric.mul_X_pderiv_pairing]

/-- All original states, with the two half-modes k and -k-1. -/
theorem oscillator_negative_positive_pairing (D : LatticeData)
    (hpos : (gramReal D).PosDef) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    oscillatorInner D hpos (current D i (-(k : ℤ) - 1) p) q =
      oscillatorInner D hpos p (current D i (k : ℤ) q) := by
  unfold oscillatorInner
  rw [current_negative, LinearMap.mulLeft_apply, map_mul, U_X]
  change D5.S3.VertexAlgebra.FactorialFockMetric.inner
    (variableImage (forwardMatrix D hpos) (i, k) * U D hpos p) (U D hpos q) = _
  rw [factorial_variable_lowering_pairing,
    ← U_positiveDerivation, positiveDerivation_current]

theorem oscillator_positive_negative_pairing (D : LatticeData)
    (hpos : (gramReal D).PosDef) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    oscillatorInner D hpos (current D i (k : ℤ) p) q =
      oscillatorInner D hpos p (current D i (-(k : ℤ) - 1) q) := by
  rw [← oscillatorInner_conj_swap,
    ← oscillator_negative_positive_pairing, oscillatorInner_conj_swap]

/-- The original half-current formal adjoint law for every integer mode. -/
theorem oscillator_current_pairing (D : LatticeData) (hpos : (gramReal D).PosDef)
    (i : Fin D.rank) (j : ℤ) (p q : Oscillator D) :
    (oscillatorCore D hpos).inner (current D i j p) q =
      (oscillatorCore D hpos).inner p (current D i (-j - 1) q) := by
  change oscillatorInner D hpos (current D i j p) q =
    oscillatorInner D hpos p (current D i (-j - 1) q)
  by_cases hj : j < 0
  · let k := (-j - 1).toNat
    have hjk : j = -(k : ℤ) - 1 := by dsimp [k]; omega
    rw [hjk]
    simpa only [show -(-(k : ℤ) - 1) - 1 = (k : ℤ) by omega] using
      oscillator_negative_positive_pairing D hpos i k p q
  · let k := j.toNat
    have hjk : j = (k : ℤ) := by dsimp [k]; omega
    rw [hjk]
    exact oscillator_positive_negative_pairing D hpos i k p q

end D5.S3.VertexAlgebra.OriginalCurrentMetric
