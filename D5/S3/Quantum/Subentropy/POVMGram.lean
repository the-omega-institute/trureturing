/- GID: D5/S3/Quantum/Subentropy/POVMGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/POVMGram
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Label-preserving positive Gram decomposition induced by a finite POVM. -/

import D5.S3.Quantum.Subentropy.ClassicalQuantumGram
import D5.S3.Quantum.Subentropy.GuessingProbability
import D5.S3.Quantum.Subentropy.PinchingGap

/-! The outcome label in each positive Gram piece determines its success contribution. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra

namespace D5.S3.Quantum.Subentropy.POVMGram

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open _root_.D5.S3.Quantum.Subentropy.GuessingProbability
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.PinchingGap

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

/-- The coordinate projection onto the fragment space carrying the specified label. -/
def blockProjector (x : X) : Matrix (X × B) (X × B) ℂ :=
  Matrix.diagonal (fun i => if i.1 = x then 1 else 0)

/-- A POVM outcome induces a positive Gram matrix while retaining its original label. -/
def povmGramPiece (p : X → ℝ) (ρ : X → DensityState B)
    (M : X → Matrix B B ℂ) (x : X) : Matrix (X × B) (X × B) ℂ :=
  (cqRowSqrt p ρ).conjTranspose * M x * cqRowSqrt p ρ

private theorem row_block_contraction (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (x : X) :
    ((cqRowSqrt p ρ * blockProjector (B := B) x : Matrix B (X × B) ℂ) *
      (cqRowSqrt p ρ).conjTranspose : Matrix B B ℂ) =
      p x • CStarMatrix.ofMatrix.symm (ρ x).1 := by
  let R : Matrix B B ℂ := CFC.sqrt (p x • CStarMatrix.ofMatrix.symm (ρ x).1)
  have hR : R.conjTranspose = R :=
    (CFC.sqrt_nonneg (p x • CStarMatrix.ofMatrix.symm (ρ x).1)).isSelfAdjoint.star_eq
  have hRsq : R * R = p x • CStarMatrix.ofMatrix.symm (ρ x).1 :=
    CFC.sqrt_mul_sqrt_self _ ((density_posSemidef (ρ x)).smul (hp x)).nonneg
  have heq : ((cqRowSqrt p ρ * blockProjector (B := B) x : Matrix B (X × B) ℂ) *
      (cqRowSqrt p ρ).conjTranspose : Matrix B B ℂ) =
      R * R.conjTranspose := by
    ext b c
    conv_lhs => rw [Matrix.mul_apply]
    conv_rhs => rw [Matrix.mul_apply]
    simp only [blockProjector, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  rw [heq, hR, hRsq]

private theorem labelled_trace (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (M : X → Matrix B B ℂ) (x : X) :
    trace (blockProjector x * povmGramPiece p ρ M x) =
      p x • trace (M x * CStarMatrix.ofMatrix.symm (ρ x).1) := by
  let V := cqRowSqrt p ρ
  calc
    _ = trace ((blockProjector x * V.conjTranspose) * (M x * V)) := by
      simp only [povmGramPiece, V, Matrix.mul_assoc]
    _ = trace ((M x * V) * (blockProjector x * V.conjTranspose)) :=
      Matrix.trace_mul_comm _ _
    _ = trace (M x * ((V * blockProjector (B := B) x : Matrix B (X × B) ℂ) * V.conjTranspose : Matrix B B ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [show ((V * blockProjector (B := B) x : Matrix B (X × B) ℂ) * V.conjTranspose : Matrix B B ℂ) =
        p x • CStarMatrix.ofMatrix.symm (ρ x).1 from row_block_contraction p hp ρ x,
        Matrix.mul_smul, Matrix.trace_smul]

private theorem povm_gram_decomposition (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (M : X → Matrix B B ℂ)
    (hM : ∀ x, (M x).PosSemidef) (hsM : ∑ x, M x = 1) :
    (∀ x, (povmGramPiece p ρ M x).PosSemidef) ∧
    (∑ x, povmGramPiece p ρ M x) = (cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ ∧
    (∀ x, ((cqRowSqrt p ρ * blockProjector (B := B) x : Matrix B (X × B) ℂ) *
      (cqRowSqrt p ρ).conjTranspose : Matrix B B ℂ) =
      p x • CStarMatrix.ofMatrix.symm (ρ x).1) ∧
    (∑ x, (trace (blockProjector x * povmGramPiece p ρ M x)).re) =
      successProbability p ρ M := by
  refine ⟨fun x => (hM x).conjTranspose_mul_mul_same _, ?_,
    row_block_contraction p hp ρ, ?_⟩
  · simp only [povmGramPiece]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsM, Matrix.mul_one]
  · unfold successProbability
    apply Finset.sum_congr rfl
    intro x _
    rw [labelled_trace p hp ρ M x]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]

private theorem labelled_pure_decomposition
    (G : X → Matrix (X × B) (X × B) ℂ) (hG : ∀ x, (G x).PosSemidef)
    (htr : trace (∑ x, G x) = 1) :
    ∃ (w : X × (X × B) → ℝ) (v : X × (X × B) → (X × B) → ℂ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
      (∀ k, ∑ i, star (v k i) * v k i = 1) ∧
      (∀ x, G x = ∑ j, w (x,j) • Matrix.vecMulVec (v (x,j)) (star (v (x,j)))) ∧
      (∑ k, w k * ∑ b, Complex.normSq (v k (k.1,b))) =
        ∑ x, (trace (blockProjector x * G x)).re := by
  let w : X × (X × B) → ℝ := fun k => (hG k.1).isHermitian.eigenvalues k.2
  let v : X × (X × B) → (X × B) → ℂ :=
    fun k => ⇑((hG k.1).isHermitian.eigenvectorBasis k.2)
  have hdecomp (x : X) :
      G x = ∑ j, w (x,j) • Matrix.vecMulVec (v (x,j)) (star (v (x,j))) := by
    ext a b
    conv_lhs => rw [(hG x).isHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, w, v]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmass (x : X) : ∑ j : X × B, w (x,j) = (trace (G x)).re := by
    have h := congrArg Complex.re (hG x).isHermitian.trace_eq_sum_eigenvalues
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, w]
      using h.symm
  have hblock (x : X) (u : (X × B) → ℂ) :
      trace (blockProjector x * Matrix.vecMulVec u (star u)) =
        ((∑ b, Complex.normSq (u (x,b)) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, blockProjector, Matrix.diagonal_mul,
      Matrix.vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Complex.normSq_eq_conj_mul_self]
    exact mul_comm _ _
  refine ⟨w, v, fun k => (hG k.1).eigenvalues_nonneg k.2, ?_, ?_, hdecomp, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp_rw [hmass]
    rw [← Complex.re_sum, ← Matrix.trace_sum, htr]
    rfl
  · intro k
    change star (⇑((hG k.1).isHermitian.eigenvectorBasis k.2)) ⬝ᵥ
      ⇑((hG k.1).isHermitian.eigenvectorBasis k.2) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, (hG k.1).isHermitian.eigenvectorBasis.orthonormal.1 k.2]
    norm_num
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [hdecomp x, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_smul, Matrix.trace_smul, hblock]
    simp [Complex.real_smul]

private theorem labelled_povm_pure_decomposition
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (M : X → Matrix B B ℂ)
    (hM : ∀ x, (M x).PosSemidef) (hsM : ∑ x, M x = 1) :
    ∃ (w : X × (X × B) → ℝ) (v : X × (X × B) → (X × B) → ℂ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
      (∀ k, ∑ i, star (v k i) * v k i = 1) ∧
      (∀ x, povmGramPiece p ρ M x =
        ∑ j, w (x,j) • Matrix.vecMulVec (v (x,j)) (star (v (x,j)))) ∧
      (cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ =
        ∑ k, w k • Matrix.vecMulVec (v k) (star (v k)) ∧
      (∑ k, w k * ∑ b, Complex.normSq (v k (k.1,b))) =
        successProbability p ρ M := by
  obtain ⟨hpsd, hsum, _, hsuccess⟩ := povm_gram_decomposition p hp ρ M hM hsM
  have htr : trace (∑ x, povmGramPiece p ρ M x) = 1 := by
    rw [hsum, Matrix.trace_mul_comm]
    rw [row_mul_adjoint p hp ρ, Matrix.trace_sum]
    simp only [Matrix.trace_smul, show ∀ x, trace
      (CStarMatrix.ofMatrix.symm (ρ x).1) = 1 from fun x => (ρ x).2.2,
      Complex.real_smul, mul_one, ← Complex.ofReal_sum, hs, Complex.ofReal_one]
  obtain ⟨w, v, hw, hws, hv, hpieces, hblock⟩ :=
    labelled_pure_decomposition _ hpsd htr
  refine ⟨w, v, hw, hws, hv, hpieces, ?_, hblock.trans hsuccess⟩
  rw [← hsum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun x _ => hpieces x)

private theorem cq_conditional_le_one_sub_success
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (M : X → Matrix B B ℂ)
    (hM : ∀ x, (M x).PosSemidef) (hsM : ∑ x, M x = 1) (i₀ : X × B) :
    conditionalSubentropy p hp hs ρ ≤ 1 - successProbability p ρ M := by
  obtain ⟨w, v, hw, hws, hv, hpieces, htotal, hsuccess⟩ :=
    labelled_povm_pure_decomposition p hp hs ρ M hM hsM
  let R : X × (X × B) → Matrix (X × B) (X × B) ℂ :=
    fun k => Matrix.vecMulVec (v k) (star (v k))
  have hstates (k : X × (X × B)) : (R k).PosSemidef ∧ (R k).trace = 1 := by
    refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
    change (∑ i, v k i * star (v k i)) = 1
    simpa only [mul_comm] using hv k
  have hj := (actual_pinching_gap_laws i₀).1.map_sum_le
    (t := Finset.univ) (w := w) (p := R)
    (fun k _ => hw k) hws (fun k _ => hstates k)
  change matrixSubentropy (blockPinch (∑ k, w k • R k)) -
      matrixSubentropy (∑ k, w k • R k) ≤
      ∑ k, w k * (matrixSubentropy (blockPinch (R k)) - matrixSubentropy (R k)) at hj
  rw [cq_conditional_eq_pinchingGap]
  calc
    _ ≤ ∑ k, w k * (matrixSubentropy (blockPinch (R k)) - matrixSubentropy (R k)) := by
      simpa only [R, ← htotal] using hj
    _ ≤ ∑ k, w k * (1 - ∑ b, Complex.normSq (v k (k.1,b))) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left ((pure_block_pinching (v k) (hv k)).2 k.1) (hw k)
    _ = 1 - successProbability p ρ M := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hws, hsuccess]

/-- Conditional subentropy is bounded by one minus the optimal POVM success
probability, hence by its negative logarithm. Zero weights and singular states
are included, and no maximizing measurement is assumed to exist. -/
theorem cq_conditional_subentropy_guessing
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    conditionalSubentropy p hp hs ρ ≤ 1 - pGuess p ρ ∧
      1 - pGuess p ρ ≤ -Real.log (pGuess p ρ) := by
  classical
  have hex : ∃ x, 0 < p x := by
    by_contra h
    push Not at h
    have hz := Finset.sum_nonpos (fun x (_ : x ∈ Finset.univ) => h x)
    rw [hs] at hz
    norm_num at hz
  obtain ⟨x, hx⟩ := hex
  haveI : Nonempty B := by
    by_contra h
    haveI : IsEmpty B := not_nonempty_iff.mp h
    have ht := (ρ x).2.2
    simpa [Matrix.trace] using ht
  let i₀ : X × B := (x, Classical.choice inferInstance)
  have hprob := pGuess_bounds p hp hs ρ
  refine ⟨hprob.2.2.2.2.2 _ ?_, hprob.2.2.2.2.1⟩
  intro M hM hsM
  exact cq_conditional_le_one_sub_success p hp hs ρ M hM hsM i₀

end D5.S3.Quantum.Subentropy.POVMGram
