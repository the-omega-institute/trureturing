/- GID: D5/S3/Arith/Robin/OriginalResidualResponseAdjoint
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalResidualResponseAdjoint
   mirror-E: none(waiver:finite-analytic-inequality)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: The original response adjoint has exact weighted moments, the original coefficient pairing identity and both coordinate signs. -/

import D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
import D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
import Mathlib.Tactic

/-! Orthogonal residual of the original Mobius floor response. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix

namespace D5.S3.Arith.Robin.OriginalResidualResponseAdjoint

open D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
  (w v gram delta c omega coeff response_projection_interface)
open D5.S3.Arith.Robin.OriginalResidualFiniteTransfer (response)

/-- The original response's right side, with the original weights and basis. -/
def responseAdjointRhs (N : ℕ) : Fin 2 → ℝ :=
  fun i => ∑ m ∈ Finset.Ico N (2 * N), w m * response N m * v N m i

/-- The inverse of the SAME original full Gram acts on that response right side. -/
def responseAdjointCoordinates (N : ℕ) : Fin 2 → ℝ :=
  (gram N)⁻¹ *ᵥ responseAdjointRhs N

/-- Adjoint response residual; only its original block is used below. -/
def responseAdjointResidual (N m : ℕ) : ℝ :=
  response N m - responseAdjointCoordinates N 0 -
    responseAdjointCoordinates N 1 * ((m : ℝ) / N)

private lemma responseAdjoint_normal_equations {N : ℕ} (hN : 3 ≤ N) :
    gram N 0 0 * responseAdjointCoordinates N 0 +
        gram N 0 1 * responseAdjointCoordinates N 1 = responseAdjointRhs N 0 ∧
    gram N 0 1 * responseAdjointCoordinates N 0 +
        gram N 1 1 * responseAdjointCoordinates N 1 = responseAdjointRhs N 1 := by
  have hi := response_projection_interface hN
  have hentries := hi.1
  have hdet : (gram N).det = delta N := by
    rw [Matrix.det_fin_two, hentries.2.2.1]
    unfold delta
    ring
  have hu : IsUnit (gram N).det :=
    isUnit_iff_ne_zero.mpr (by rw [hdet]; exact hi.2.1.ne')
  have he : gram N *ᵥ responseAdjointCoordinates N = responseAdjointRhs N := by
    unfold responseAdjointCoordinates
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  constructor
  · have h0 := congrFun he (0 : Fin 2)
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · have h1 := congrFun he (1 : Fin 2)
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      hentries.2.2.1] using h1

private lemma responseAdjoint_exact_moments {N : ℕ} (hN : 3 ≤ N) :
    (∑ m ∈ Finset.Ico N (2 * N), w m * responseAdjointResidual N m) = 0 ∧
    (∑ m ∈ Finset.Ico N (2 * N),
      (w m * ((m : ℝ) / N)) * responseAdjointResidual N m) = 0 := by
  rcases responseAdjoint_normal_equations hN with ⟨h0, h1⟩
  rcases (response_projection_interface hN).1 with ⟨h00, h01, _, h11⟩
  have he0 : (∑ m ∈ Finset.Ico N (2 * N), w m * responseAdjointResidual N m) =
      responseAdjointRhs N 0 -
        responseAdjointCoordinates N 0 * gram N 0 0 -
        responseAdjointCoordinates N 1 * gram N 0 1 := by
    rw [h00, h01]
    simp only [responseAdjointRhs, v, Matrix.cons_val_zero, mul_one]
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    unfold responseAdjointResidual
    ring
  have he1 : (∑ m ∈ Finset.Ico N (2 * N),
        (w m * ((m : ℝ) / N)) * responseAdjointResidual N m) =
      responseAdjointRhs N 1 -
        responseAdjointCoordinates N 0 * gram N 0 1 -
        responseAdjointCoordinates N 1 * gram N 1 1 := by
    rw [h01, h11]
    simp only [responseAdjointRhs, v, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    unfold responseAdjointResidual
    ring
  exact ⟨by linarith [he0], by linarith [he1]⟩

private lemma responseAdjoint_coeff_ratio_moment {N : ℕ} (hN : 3 ≤ N) (a b : ℝ) :
    (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * ((m : ℝ) / N)) = 0 := by
  have hm := ((response_projection_interface hN).2.2.1 a b).2
  calc
    _ = (∑ m ∈ Finset.Ico N (2 * N), (m : ℝ) * coeff N a b m) / (N : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = 0 := by rw [hm, zero_div]

theorem responseAdjoint_actual_identity {N : ℕ} (hN : 3 ≤ N) (a b : ℝ) :
    D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) =
      Real.log (N : ℝ) *
        ∑ m ∈ Finset.Ico N (2 * N), omega a b m * responseAdjointResidual N m := by
  have hcm0 := ((response_projection_interface hN).2.2.1 a b).1
  have hcm1 := responseAdjoint_coeff_ratio_moment hN a b
  have hem := responseAdjoint_exact_moments hN
  have hremoveResponse :
      (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * responseAdjointResidual N m) =
        ∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * response N m := by
    have hsplit :
        (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * responseAdjointResidual N m) =
          (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * response N m) -
            responseAdjointCoordinates N 0 *
              (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m) -
            responseAdjointCoordinates N 1 *
              (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * ((m : ℝ) / N)) := by
      rw [Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m _
      unfold responseAdjointResidual
      ring
    simpa only [hcm0, hcm1, mul_zero, sub_zero] using hsplit
  have hremoveDatum :
      (∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * responseAdjointResidual N m) =
        Real.log (N : ℝ) *
          (∑ m ∈ Finset.Ico N (2 * N), omega a b m * responseAdjointResidual N m) -
        c N a b 0 *
          (∑ m ∈ Finset.Ico N (2 * N), w m * responseAdjointResidual N m) -
        c N a b 1 *
          (∑ m ∈ Finset.Ico N (2 * N),
            (w m * ((m : ℝ) / N)) * responseAdjointResidual N m) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [(response_projection_interface hN).2.2.2 a b m hm]
    ring
  calc
    _ = ∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * response N m := rfl
    _ = ∑ m ∈ Finset.Ico N (2 * N), coeff N a b m * responseAdjointResidual N m :=
      hremoveResponse.symm
    _ = _ := by simpa only [hem.1, hem.2, mul_zero, sub_zero] using hremoveDatum

private lemma responseAdjoint_nonzero {N : ℕ} (hN : 3 ≤ N) :
    ∃ m ∈ Finset.Ico N (2 * N), responseAdjointResidual N m ≠ 0 := by
  classical
  by_contra hzero
  push_neg at hzero
  apply D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate.response_not_affine_on_original_block hN
  refine ⟨responseAdjointCoordinates N 0, responseAdjointCoordinates N 1, ?_⟩
  intro m hm
  have hz := hzero m hm
  unfold responseAdjointResidual at hz
  linarith

private lemma responseAdjoint_both_signs {N : ℕ} (hN : 3 ≤ N) :
    (∃ m ∈ Finset.Ico N (2 * N), 0 < responseAdjointResidual N m) ∧
    (∃ m ∈ Finset.Ico N (2 * N), responseAdjointResidual N m < 0) := by
  classical
  have hz := (responseAdjoint_exact_moments hN).1
  have hne := responseAdjoint_nonzero hN
  constructor
  · by_contra hno
    push_neg at hno
    have hsign : ∀ m ∈ Finset.Ico N (2 * N), w m * responseAdjointResidual N m ≤ 0 := by
      intro m hm
      exact mul_nonpos_of_nonneg_of_nonpos (by unfold w; positivity) (hno m hm)
    have heach := (Finset.sum_eq_zero_iff_of_nonpos hsign).mp hz
    obtain ⟨m, hm, hnonzero⟩ := hne
    have hmpos : 0 < m := by have := (Finset.mem_Ico.mp hm).1; omega
    have hw : 0 < w m := by unfold w; positivity
    exact hnonzero ((mul_eq_zero.mp (heach m hm)).resolve_left hw.ne')
  · by_contra hno
    push_neg at hno
    have hsign : ∀ m ∈ Finset.Ico N (2 * N), 0 ≤ w m * responseAdjointResidual N m := by
      intro m hm
      exact mul_nonneg (by unfold w; positivity) (hno m hm)
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hsign).mp hz
    obtain ⟨m, hm, hnonzero⟩ := hne
    have hmpos : 0 < m := by have := (Finset.mem_Ico.mp hm).1; omega
    have hw : 0 < w m := by unfold w; positivity
    exact hnonzero ((mul_eq_zero.mp (heach m hm)).resolve_left hw.ne')

open Finset
open D5.S3.Arith.Robin.OriginalResidualPartialCellWeights (or6_partialCell_variation)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g)

/-- Reused r2079 cell localization, specialized to the requested thirds.
The coefficient family itself is the full original affine projection;
only its omega pairing localizes to one row. -/
private theorem responseAdjoint_strict_cell {N m : ℕ} (hN : 3 ≤ N)
    (hm : m ∈ Ico N (2 * N)) :
    (N : ℝ) < (m : ℝ) + 1 / 3 ∧
    (m : ℝ) + 1 / 3 < (m : ℝ) + 2 / 3 ∧
    (m : ℝ) + 2 / 3 < 2 * (N : ℝ) ∧
    0 < g ((m : ℝ) + 1 / 3) - g ((m : ℝ) + 2 / 3) ∧
    (∀ j : ℕ,
      omega ((m : ℝ) + 1 / 3) ((m : ℝ) + 2 / 3) j =
        if j = m then g ((m : ℝ) + 1 / 3) - g ((m : ℝ) + 2 / 3) else 0) ∧
    D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N
      (coeff N ((m : ℝ) + 1 / 3) ((m : ℝ) + 2 / 3)) =
        (Real.log (N : ℝ) *
          (g ((m : ℝ) + 1 / 3) - g ((m : ℝ) + 2 / 3))) *
            responseAdjointResidual N m := by
  classical
  let a : ℝ := (m : ℝ) + 1 / 3
  let b : ℝ := (m : ℝ) + 2 / 3
  have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast (mem_Ico.mp hm).1
  have hmN : (m : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 2 * N by have := (mem_Ico.mp hm).2; omega)
  have hNa : (N : ℝ) < a := by dsimp only [a]; linarith
  have hab : a < b := by dsimp only [a, b]; linarith
  have hbN : b < 2 * (N : ℝ) := by dsimp only [b]; linarith
  have ham : (m : ℝ) ≤ a := by dsimp only [a]; linarith
  have hbm : b ≤ (m : ℝ) + 1 := by dsimp only [b]; linarith
  have hω := (or6_partialCell_variation hN hNa hab hbN).1
  have hown : omega a b m = g a - g b := by
    rw [hω m, max_eq_left ham, min_eq_left hbm, if_pos hab]
  have ha1 : 1 < a :=
    (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega)).trans hNa
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans hab
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab.le
  have hden : a * Real.log a < b * Real.log b := by
    calc
      _ < b * Real.log a := mul_lt_mul_of_pos_right hab hla
      _ ≤ _ := mul_le_mul_of_nonneg_left hlab hb0.le
  have hg : g b < g a := by
    unfold g
    exact one_div_lt_one_div_of_lt (mul_pos ha0 hla) hden
  have hsupport (j : ℕ) : omega a b j = if j = m then g a - g b else 0 := by
    by_cases hj : j = m
    · subst j
      simpa using hown
    · have hno : ¬ max a (j : ℝ) < min b ((j : ℝ) + 1) := by
        rcases lt_or_gt_of_ne hj with hjm | hmj
        · have hjmR : (j : ℝ) + 1 ≤ (m : ℝ) := by
            exact_mod_cast (show j + 1 ≤ m by omega)
          have hleft : a ≤ max a (j : ℝ) := le_max_left _ _
          have hright : min b ((j : ℝ) + 1) ≤ (j : ℝ) + 1 := min_le_right _ _
          intro hbad
          linarith
        · have hmjR : (m : ℝ) + 1 ≤ (j : ℝ) := by
            exact_mod_cast (show m + 1 ≤ j by omega)
          have hleft : (j : ℝ) ≤ max a (j : ℝ) := le_max_right _ _
          have hright : min b ((j : ℝ) + 1) ≤ b := min_le_left _ _
          intro hbad
          linarith
      rw [hω j, if_neg hno, if_neg hj]
  have hsum :
      (∑ j ∈ Ico N (2 * N), omega a b j * responseAdjointResidual N j) =
        (g a - g b) * responseAdjointResidual N m := by
    calc
      _ = omega a b m * responseAdjointResidual N m := by
        apply Finset.sum_eq_single m
        · intro j _ hjm
          rw [hsupport j, if_neg hjm, zero_mul]
        · intro hnot
          exact (hnot hm).elim
      _ = _ := by rw [hown]
  change (N : ℝ) < a ∧ a < b ∧ b < 2 * (N : ℝ) ∧
    0 < g a - g b ∧ (∀ j : ℕ, omega a b j = if j = m then g a - g b else 0) ∧
    D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) =
      (Real.log (N : ℝ) * (g a - g b)) * responseAdjointResidual N m
  refine ⟨hNa, hab, hbN, sub_pos.mpr hg, hsupport, ?_⟩
  rw [responseAdjoint_actual_identity hN, hsum]
  ring

/-- The existing r2079 existence proof is consumed PRIVATELY by the original
bundle below, without adding another public strict-realization wrapper. -/
private theorem responseAdjoint_strict_residual_both_signs {N : ℕ} (hN : 3 ≤ N) :
    (∃ a b : ℝ, (N : ℝ) < a ∧ a < b ∧ b < 2 * (N : ℝ) ∧
      0 < D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b)) ∧
    (∃ a b : ℝ, (N : ℝ) < a ∧ a < b ∧ b < 2 * (N : ℝ) ∧
      D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) < 0) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rcases responseAdjoint_both_signs hN with ⟨hpositive, hnegative⟩
  constructor
  · obtain ⟨m, hm, hsign⟩ := hpositive
    rcases responseAdjoint_strict_cell hN hm with ⟨hNa, hab, hbN, hmass, _, hreadout⟩
    refine ⟨(m : ℝ) + 1 / 3, (m : ℝ) + 2 / 3, hNa, hab, hbN, ?_⟩
    rw [hreadout]
    exact mul_pos (mul_pos hlog hmass) hsign
  · obtain ⟨m, hm, hsign⟩ := hnegative
    rcases responseAdjoint_strict_cell hN hm with ⟨hNa, hab, hbN, hmass, _, hreadout⟩
    refine ⟨(m : ℝ) + 1 / 3, (m : ℝ) + 2 / 3, hNa, hab, hbN, ?_⟩
    rw [hreadout]
    exact mul_neg_of_pos_of_neg (mul_pos hlog hmass) hsign

/-- The original six-clause adjoint bundle, enhanced with actual positive
and negative residuals at freely chosen legal strict intervals. The original
all-real identity, original block and all six prior clauses are preserved. -/
theorem or6_response_adjoint_identity_and_signs {N : ℕ} (hN : 3 ≤ N) :
    (∑ m ∈ Finset.Ico N (2 * N), w m * responseAdjointResidual N m) = 0 ∧
    (∑ m ∈ Finset.Ico N (2 * N),
      (w m * ((m : ℝ) / N)) * responseAdjointResidual N m) = 0 ∧
    (∀ a b : ℝ,
      D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) =
        Real.log (N : ℝ) *
          ∑ m ∈ Finset.Ico N (2 * N), omega a b m * responseAdjointResidual N m) ∧
    (∃ m ∈ Finset.Ico N (2 * N), responseAdjointResidual N m ≠ 0) ∧
    (∃ m ∈ Finset.Ico N (2 * N), 0 < responseAdjointResidual N m) ∧
    (∃ m ∈ Finset.Ico N (2 * N), responseAdjointResidual N m < 0) ∧
    (∃ a b : ℝ, (N : ℝ) < a ∧ a < b ∧ b < 2 * (N : ℝ) ∧
      0 < D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b)) ∧
    (∃ a b : ℝ, (N : ℝ) < a ∧ a < b ∧ b < 2 * (N : ℝ) ∧
      D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual N (coeff N a b) < 0) := by
  have hm := responseAdjoint_exact_moments hN
  have hs := responseAdjoint_both_signs hN
  have hr := responseAdjoint_strict_residual_both_signs hN
  exact ⟨hm.1, hm.2, responseAdjoint_actual_identity hN,
    responseAdjoint_nonzero hN, hs.1, hs.2, hr.1, hr.2⟩


end D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
