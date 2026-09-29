/- GID: D5/S3/Quantum/Recovery/FiniteKrausReversibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteKrausReversibility
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Scalar error products construct a finite normalized Kraus left inverse. -/

import D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
import Mathlib.Analysis.Matrix.PosDef

/-!
# Exact finite Kraus reversibility

The spectral theorem and positive eigenvalues are reused from Mathlib. The
orthogonal-syndrome recovery and full-space completion are reused from their
existing owners. Zero spectral weights are removed by an actual subtype sum;
there is no division by a zero probability. The only local mixing calculation
is rectangular: the existing repository Kraus-mixing result has square Kraus
matrices and cannot directly type this input/output pair.

The construction quantifies over finite Kraus representations. It does not
assume a representation theorem for the separately bundled all-amplification
CP interface.

The criterion and construction are classical Knill--Laflamme and Nayak--Sen
results. No new correction criterion is claimed.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.FiniteKrausReversibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
open D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel

variable {s n d : Type*} [Fintype s] [DecidableEq s]
  [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]

private def rotateErrors (E : s → Matrix n d ℂ) (V : Matrix s s ℂ) (j : s) :
    Matrix n d ℂ := ∑ a, V a j • E a

private theorem rotated_gram (E : s → Matrix n d ℂ) (c V : Matrix s s ℂ)
    (hE : ∀ a b, (E a)ᴴ * E b = c a b • (1 : Matrix d d ℂ)) (j k : s) :
    (rotateErrors E V j)ᴴ * rotateErrors E V k =
      (Vᴴ * c * V) j k • (1 : Matrix d d ℂ) := by
  calc
    _ = ∑ b, ∑ a, (star (V a j) * c a b * V b k) • (1 : Matrix d d ℂ) := by
      simp only [rotateErrors, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hE]
      simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul, Finset.sum_smul]

private theorem rotated_action (E : s → Matrix n d ℂ) (V : Matrix s s ℂ)
    (hV : V * Vᴴ = 1) (X : Matrix d d ℂ) :
    (∑ j, rotateErrors E V j * X * (rotateErrors E V j)ᴴ) =
      ∑ a, E a * X * (E a)ᴴ := by
  have hcoeff (a b : s) : (∑ j, V a j * star (V b j)) =
      if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix s s ℂ => M a b) hV
  calc
    _ = ∑ j, ∑ a, ∑ b, (V a j * star (V b j)) • (E a * X * (E b)ᴴ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [rotateErrors, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
      rw [Finset.sum_comm]
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp [smul_smul, mul_comm]
    _ = ∑ a, ∑ b, (∑ j, V a j * star (V b j)) • (E a * X * (E b)ᴴ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = _ := by simp_rw [hcoeff]; simp

/-- The scalar criterion builds a finite, normalized, actual left inverse. All zero eigenvalue errors are explicitly eliminated. -/
theorem scalar_products_construct_left_inverse (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1) (v : d) (c : Matrix s s ℂ)
    (hE : ∀ a b, (E a)ᴴ * E b = c a b • (1 : Matrix d d ℂ)) :
    ∃ r : ℕ, ∃ A : Fin r → Matrix d n ℂ,
      (∑ b, (A b)ᴴ * A b) = 1 ∧
      ∀ X : Matrix d d ℂ,
        (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X := by
  classical
  let R : Matrix n s ℂ := fun x a => E a x v
  have hcGram : c = Rᴴ * R := by
    ext a b
    have h := congrArg (fun M : Matrix d d ℂ => M v v) (hE a b)
    change c a b = ∑ j, star (E a j v) * E b j v
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using h.symm
  have hc : c.PosSemidef := by rw [hcGram]; exact Matrix.posSemidef_conjTranspose_mul_self R
  have hcTrace : Matrix.trace c = 1 := by
    have h := congrArg (fun M : Matrix d d ℂ => M v v) hTP
    have hdiag (a : s) : ((E a)ᴴ * E a) v v = c a a := by
      simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using
        congrArg (fun M : Matrix d d ℂ => M v v) (hE a a)
    simpa only [Matrix.sum_apply, hdiag, Matrix.one_apply_eq, Matrix.trace,
      Matrix.diag_apply] using h
  let lam : s → ℝ := hc.isHermitian.eigenvalues
  let V : Matrix.unitaryGroup s ℂ := hc.isHermitian.eigenvectorUnitary
  let F : s → Matrix n d ℂ := rotateErrors E V
  have hlam (j : s) : 0 ≤ lam j := hc.eigenvalues_nonneg j
  have hV : (V : Matrix s s ℂ) * (V : Matrix s s ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self V
  have hdiagV : (V : Matrix s s ℂ)ᴴ * c * (V : Matrix s s ℂ) =
      Matrix.diagonal (fun j => (lam j : ℂ)) := by
    simpa [V, lam, Unitary.conjStarAlgAut_star_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def] using
        hc.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hFgram (j k : s) : (F j)ᴴ * F k =
      if j = k then (lam j : ℂ) • (1 : Matrix d d ℂ) else 0 := by
    change (rotateErrors E V j)ᴴ * rotateErrors E V k = _
    rw [rotated_gram E c V hE, hdiagV]
    by_cases h : j = k
    · subst k; simp
    · simp [Matrix.diagonal_apply, h]
  have hzero (j : s) (hj : ¬ 0 < lam j) : F j = 0 := by
    have hl : lam j = 0 := le_antisymm (le_of_not_gt hj) (hlam j)
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa [hFgram j j, hl]
  have hlamSum : (∑ j, (lam j : ℂ)) = 1 := by
    have hsum : Matrix.trace c = ∑ j, (lam j : ℂ) := by
      change Matrix.trace c = ∑ j, (hc.isHermitian.eigenvalues j : ℂ)
      exact hc.isHermitian.trace_eq_sum_eigenvalues
    exact hsum.symm.trans hcTrace
  let J := {j : s // 0 < lam j}
  let S : J → Matrix n d ℂ := fun j => (Real.sqrt (lam j) : ℂ)⁻¹ • F j
  have hroot (j : J) : (Real.sqrt (lam j) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 j.property)
  have hrootsq (j : J) : (Real.sqrt (lam j) : ℂ) ^ 2 = (lam j : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hlam j)
  have hS : OrthogonalSyndromes S := by
    intro j k
    change (((Real.sqrt (lam j) : ℂ)⁻¹ • F j)ᴴ *
      ((Real.sqrt (lam k) : ℂ)⁻¹ • F k)) = _
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hstar : star ((Real.sqrt (lam j) : ℂ)⁻¹) = (Real.sqrt (lam j) : ℂ)⁻¹ := by simp
    rw [hstar, hFgram]
    by_cases h : j = k
    · subst k
      simp only [if_true, smul_smul]
      have hz : (Real.sqrt (lam j) : ℂ)⁻¹ * (Real.sqrt (lam j) : ℂ)⁻¹ * (lam j : ℂ) = 1 := by
        rw [← hrootsq j]
        field_simp [hroot j]
      rw [hz, one_smul]
    · have hjk : (j : s) ≠ (k : s) := fun he => h (Subtype.ext he)
      simp [h, hjk]
  have hFrep (j : J) : F j = (Real.sqrt (lam j) : ℂ) • S j := by
    dsimp only [S]
    rw [smul_smul, mul_inv_cancel₀ (hroot j), one_smul]
  let sigma : Matrix J J ℂ := Matrix.diagonal (fun j => (lam j : ℂ))
  have hsigmatrace : Matrix.trace sigma = 1 := by
    dsimp only [sigma]
    rw [Matrix.trace_diagonal]
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j => 0 < lam j)
      (fun j => (lam j : ℂ))
    have hz : (∑ j : {j : s // ¬ 0 < lam j}, (lam j : ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hl : lam j = 0 := le_antisymm (le_of_not_gt j.property) (hlam j)
      simp [hl]
    have hpositive : (∑ j, (lam j : ℂ)) = ∑ j : J, (lam j : ℂ) := by
      simpa only [hz, add_zero] using hsplit.symm
    rw [← hpositive]
    exact hlamSum
  have hnoise (X : Matrix d d ℂ) :
      (∑ a, E a * X * (E a)ᴴ) = syndromeEncoding S sigma X := by
    calc
      _ = ∑ j, F j * X * (F j)ᴴ := (rotated_action E V hV X).symm
      _ = ∑ j : J, F j * X * (F j)ᴴ := by
        have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j => 0 < lam j)
          (fun j => F j * X * (F j)ᴴ)
        have hz : (∑ j : {j : s // ¬ 0 < lam j}, F j * X * (F j)ᴴ) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hzero j j.property]
          simp
        simpa only [hz, add_zero] using hsplit.symm
      _ = ∑ j : J, (lam j : ℂ) • (S j * X * (S j)ᴴ) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = ((Real.sqrt (lam j) : ℂ) • S j) * X *
              (((Real.sqrt (lam j) : ℂ) • S j)ᴴ) :=
            congrArg (fun M : Matrix n d ℂ => M * X * Mᴴ) (hFrep j)
          _ = _ := by
            simp only [Matrix.conjTranspose_smul, Matrix.smul_mul,
              Matrix.mul_smul, smul_smul]
            have hs : star (Real.sqrt (lam j) : ℂ) = (Real.sqrt (lam j) : ℂ) := by simp
            rw [hs]
            have hsq : (Real.sqrt (lam j) : ℂ) * (Real.sqrt (lam j) : ℂ) = (lam j : ℂ) := by
              simpa only [pow_two] using hrootsq j
            rw [hsq]
      _ = syndromeEncoding S sigma X := by
        simp only [syndromeEncoding, sigma, Matrix.diagonal_apply, ite_smul,
          zero_smul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_eq_single j]
        · simp
        · intro k hk hkj
          simp [Ne.symm hkj]
        · simp
  let P := codeSupport S
  let A₀ : J ⊕ n → Matrix d n ℂ := completeKraus (fun j => (S j)ᴴ) P v
  have hP : Pᴴ = P := by
    simp [P, codeSupport, logicalRepresentation, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hPP : P * P = P := by
    simpa [P, codeSupport] using logical_representation_mul S hS (1 : Matrix d d ℂ) 1
  have hbase : (∑ j, ((S j)ᴴ)ᴴ * (S j)ᴴ) = P := by
    simp [P, codeSupport, logicalRepresentation]
  have hA₀ : (∑ b, (A₀ b)ᴴ * A₀ b) = 1 := by
    have hRowUnit :
        (∑ j : n, (Matrix.single v j (1 : ℂ))ᴴ * Matrix.single v j (1 : ℂ)) =
          (1 : Matrix n n ℂ) := by
      calc
        _ = ∑ j : n, Matrix.single j j (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simpa only [Matrix.conjTranspose_single, star_one, one_mul] using
            (Matrix.single_mul_single_same (c := (1 : ℂ)) j v j (1 : ℂ))
        _ = 1 := Matrix.sum_single_one
    have hRowGram :
        (∑ j : n, (rowReset v (1 - P) j)ᴴ * rowReset v (1 - P) j) =
          (1 - P)ᴴ * (1 - P) := by
      calc
        _ = (1 - P)ᴴ * (∑ j : n,
            (Matrix.single v j (1 : ℂ))ᴴ * Matrix.single v j (1 : ℂ)) *
            (1 - P) := by
          simp only [rowReset, Matrix.conjTranspose_mul, Matrix.mul_sum,
            Matrix.sum_mul, Matrix.mul_assoc]
        _ = (1 - P)ᴴ * (1 - P) := by rw [hRowUnit, Matrix.mul_one]
    have hComp : (1 - P)ᴴ * (1 - P) = 1 - P := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        hPP, sub_self, sub_zero]
    simp only [A₀, completeKraus, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hbase, hRowGram, hComp]
    abel
  have hrec (X : Matrix d d ℂ) :
      (∑ b, A₀ b * (∑ a, E a * X * (E a)ᴴ) * (A₀ b)ᴴ) = X := by
    change (∑ b, completeKraus (fun j => (S j)ᴴ) P v b *
      (∑ a, E a * X * (E a)ᴴ) * (completeKraus (fun j => (S j)ᴴ) P v b)ᴴ) = X
    rw [complete_kraus_action _ P v hP hPP, hnoise X]
    have hsupport : P * syndromeEncoding S sigma X = syndromeEncoding S sigma X := by
      simpa only [P, codeSupport, Matrix.one_mul] using
        logical_action_on_encoding S hS 1 X sigma
    have hz : (1 - P) * syndromeEncoding S sigma X = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hsupport, sub_self]
    rw [hz, Matrix.trace_zero, zero_smul, add_zero]
    simpa only [syndromeDecoding, Matrix.conjTranspose_conjTranspose,
      hsigmatrace, one_smul] using orthogonal_syndrome_recovery S hS sigma X
  let e := (Fintype.equivFin (J ⊕ n)).symm
  refine ⟨Fintype.card (J ⊕ n), fun b => A₀ (e b), ?_, fun X => ?_⟩
  · calc
      _ = ∑ b, (A₀ b)ᴴ * A₀ b := Equiv.sum_comp e _
      _ = 1 := hA₀
  · calc
      _ = ∑ b, A₀ b * (∑ a, E a * X * (E a)ᴴ) * (A₀ b)ᴴ := Equiv.sum_comp e _
      _ = X := hrec X

#print axioms scalar_products_construct_left_inverse

end D5.S3.Quantum.Recovery.FiniteKrausReversibility
