/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickSpectral
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Spectral threshold separation and the common-corner commutator criterion. -/

import D5.S3.Weil.ZetaLinear.HermitianPosPart
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Spectral separation of the two canonical-overlap residuals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive residual of the scalar canonical overlap at threshold `t`. -/
def thresholdPositive (D : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => max (x - t * (1 - x)) 0) D

/-- The negative residual; eigenvalues at the threshold contribute zero. -/
def thresholdNegative (D : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => max (t * (1 - x) - x) 0) D

private theorem separating_threshold {a b : ℝ}
    (hb : 0 < b) (hba : b < a) (ha : a < 1) :
    ∃ t : ℝ, 0 < t ∧ 0 < a - t * (1 - a) ∧ b - t * (1 - b) < 0 := by
  have hd : 0 < 2 - a - b := by linarith
  refine ⟨(a + b) / (2 - a - b), div_pos (by linarith) hd, ?_, ?_⟩
  · have he : a - (a + b) / (2 - a - b) * (1 - a) =
        (a - b) / (2 - a - b) := by field_simp; ring
    rw [he]
    exact div_pos (sub_pos.mpr hba) hd
  · have he : b - (a + b) / (2 - a - b) * (1 - b) =
        (b - a) / (2 - a - b) := by field_simp; ring
    rw [he]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hba) hd

private theorem diagonal_cuts_iff (d : n → ℝ) (W : Matrix n n ℂ)
    (hW : W.IsHermitian)
    (hd : ∀ i j, W i j ≠ 0 → (0 < d i ∧ d i < 1) ∧ (0 < d j ∧ d j < 1)) :
    (∀ t : ℝ, 0 < t →
      diagonal (fun i => (max (d i - t * (1 - d i)) 0 : ℝ) : n → ℂ) * W *
        diagonal (fun i => (max (t * (1 - d i) - d i) 0 : ℝ) : n → ℂ) = 0) ↔
      W * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * W := by
  classical
  have kill (h : ∀ t : ℝ, 0 < t →
      diagonal (fun i => (max (d i - t * (1 - d i)) 0 : ℝ) : n → ℂ) * W *
        diagonal (fun i => (max (t * (1 - d i) - d i) 0 : ℝ) : n → ℂ) = 0)
      (i j : n) (hji : d j < d i) : W i j = 0 := by
    by_contra hn
    obtain ⟨hdi, hdj⟩ := hd i j hn
    obtain ⟨t, ht, hi, hj⟩ := separating_threshold hdj.1 hji hdi.2
    have he := congrArg (fun M : Matrix n n ℂ => M i j) (h t ht)
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply] at he
    rw [max_eq_left (le_of_lt hi), max_eq_left (by linarith : 0 ≤ t * (1 - d j) - d j)] at he
    have hi' : (↑(d i - t * (1 - d i)) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hi
    have hj' : (↑(t * (1 - d j) - d j) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (show 0 < t * (1 - d j) - d j by linarith)
    exact hn ((mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hj')).resolve_left hi')
  constructor
  · intro h
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_trichotomy (d i) (d j) with hij | hij | hij
    · have hz := kill h j i hij
      have hstar := congrArg (fun M : Matrix n n ℂ => M i j) hW.eq
      simp only [Matrix.conjTranspose_apply, hz] at hstar
      rw [← hstar]
      simp
    · rw [hij, mul_comm]
    · rw [kill h i j hij]
      simp
  · intro h t _
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
    have he := congrArg (fun M : Matrix n n ℂ => M i j) h
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    by_cases hij : d i = d j
    · rw [hij]
      have hz : max (d j - t * (1 - d j)) 0 * max (t * (1 - d j) - d j) 0 = 0 := by
        rcases le_total (d j) (t * (1 - d j)) with hj | hj
        · rw [max_eq_right (sub_nonpos.mpr hj), zero_mul]
        · rw [max_eq_right (sub_nonpos.mpr hj), mul_zero]
      have hzc : (↑(max (d j - t * (1 - d j)) 0) : ℂ) *
          ↑(max (t * (1 - d j) - d j) 0) = 0 := by exact_mod_cast hz
      calc
        _ = ((↑(max (d j - t * (1 - d j)) 0) : ℂ) *
            ↑(max (t * (1 - d j) - d j) 0)) * W i j := by ring
        _ = 0 := by rw [hzc, zero_mul]
    · have hn : (d j : ℂ) - (d i : ℂ) ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hij)
      have hz : ((d j : ℂ) - (d i : ℂ)) * W i j = 0 := by
        calc
          _ = W i j * (d j : ℂ) - (d i : ℂ) * W i j := by ring
          _ = 0 := sub_eq_zero.mpr he
      rw [(mul_eq_zero.mp hz).resolve_left hn]
      simp

/-- If a Hermitian weight is supported on the interior spectrum of a Hermitian
matrix, its threshold cross terms vanish precisely when it commutes with that
matrix. Repeated eigenvalues and the empty matrix carrier are included. -/
theorem all_thresholds_iff_commute (D W : Matrix n n ℂ)
    (hD : D.IsHermitian) (hW : W.IsHermitian)
    (hd : ∀ i j,
      ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hD.eigenvectorUnitary).symm W) i j ≠ 0 →
        (0 < hD.eigenvalues i ∧ hD.eigenvalues i < 1) ∧
        (0 < hD.eigenvalues j ∧ hD.eigenvalues j < 1)) :
    (∀ t : ℝ, 0 < t → thresholdPositive D t * W * thresholdNegative D t = 0) ↔
      W * D = D * W := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hD.eigenvectorUnitary
  let V := e.symm W
  have hV : V.IsHermitian := by
    change star V = V
    dsimp only [V]
    rw [← map_star, hW.isSelfAdjoint.star_eq]
  have hspec : e (diagonal (fun i => (hD.eigenvalues i : ℂ))) = D := by
    simpa only [e, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hD.spectral_theorem.symm
  have hpos (t : ℝ) : thresholdPositive D t =
      e (diagonal (fun i => (max (hD.eigenvalues i - t * (1 - hD.eigenvalues i)) 0 : ℝ) : n → ℂ)) := by
    rw [thresholdPositive, hD.cfc_eq]
    rfl
  have hneg (t : ℝ) : thresholdNegative D t =
      e (diagonal (fun i => (max (t * (1 - hD.eigenvalues i) - hD.eigenvalues i) 0 : ℝ) : n → ℂ)) := by
    rw [thresholdNegative, hD.cfc_eq]
    rfl
  have hcuts : (∀ t : ℝ, 0 < t → thresholdPositive D t * W * thresholdNegative D t = 0) ↔
      (∀ t : ℝ, 0 < t →
        diagonal (fun i => (max (hD.eigenvalues i - t * (1 - hD.eigenvalues i)) 0 : ℝ) : n → ℂ) * V *
          diagonal (fun i => (max (t * (1 - hD.eigenvalues i) - hD.eigenvalues i) 0 : ℝ) : n → ℂ) = 0) := by
    apply forall_congr'
    intro t
    apply imp_congr_right
    intro _
    rw [hpos, hneg, show W = e V from (e.apply_symm_apply W).symm,
      ← map_mul, ← map_mul]
    constructor
    · intro h
      have hm := congrArg e.symm h
      simpa only [e.symm_apply_apply, map_zero] using hm
    · intro h
      rw [h, map_zero]
  rw [hcuts, diagonal_cuts_iff _ V hV hd]
  constructor <;> intro h
  · have hm := congrArg e h
    simpa only [map_mul, hspec, V, e.apply_symm_apply] using hm
  · rw [← hspec] at h
    have hm := congrArg e.symm h
    simpa only [map_mul, e.symm_apply_apply, V] using hm

/-- The actual spectral projection onto eigenvalues strictly between zero and one. -/
def interiorProjection (C : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => if 0 < x ∧ x < 1 then 1 else 0) C

/-- Ambient form of the common-corner spectral criterion. No invertibility of
`C` or `1-C`, no simple-spectrum hypothesis, and no nonzero-corner hypothesis
are imposed. Only the compressed weight `P W P` enters the criterion. -/
theorem all_common_thresholds_iff_commute (C W : Matrix n n ℂ)
    (hC : C.IsHermitian) (hW : W.IsHermitian) :
    let P := interiorProjection C
    (∀ t : ℝ, 0 < t →
      thresholdPositive C t * (P * W * P) * thresholdNegative C t = 0) ↔
      (P * W * P) * C = C * (P * W * P) := by
  classical
  dsimp only
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hC.eigenvectorUnitary
  let F : Matrix n n ℂ := diagonal (fun i =>
    ((if 0 < hC.eigenvalues i ∧ hC.eigenvalues i < 1 then 1 else 0 : ℝ) : ℂ))
  have hP : (interiorProjection C).IsHermitian := cfc_predicate _ C
  have hT : (interiorProjection C * W * interiorProjection C).IsHermitian := by
    change (interiorProjection C * W * interiorProjection C)ᴴ = _
    simp only [Matrix.conjTranspose_mul, hP.eq, hW.eq, Matrix.mul_assoc]
  apply all_thresholds_iff_commute C _ hC hT
  have hF : e.symm (interiorProjection C) = F := by
    have he : interiorProjection C = e F := by
      rw [interiorProjection, hC.cfc_eq]
      rfl
    rw [he, e.symm_apply_apply]
  intro i j hij
  change (e.symm (interiorProjection C * W * interiorProjection C)) i j ≠ 0 at hij
  simp only [map_mul, hF, Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  by_cases hi : 0 < hC.eigenvalues i ∧ hC.eigenvalues i < 1
  · by_cases hj : 0 < hC.eigenvalues j ∧ hC.eigenvalues j < 1
    · exact ⟨hi, hj⟩
    · exfalso
      exact hij (by simp only [F, Matrix.diagonal_mul, Matrix.mul_diagonal, if_neg hj,
        Complex.ofReal_zero, mul_zero])
  · exfalso
    exact hij (by simp only [F, Matrix.diagonal_mul, Matrix.mul_diagonal, if_neg hi,
      Complex.ofReal_zero, zero_mul])

end D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
