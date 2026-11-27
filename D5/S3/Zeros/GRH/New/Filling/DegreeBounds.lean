/- GID: D5/S3/Zeros/GRH/New/Filling/DegreeBounds
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/DegreeBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.DegreeBounds. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/DegreeBounds.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.BesselGeneric
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Last step: pairing on the top group is a multiple of the branching restriction. Bounds
on the Bessel degree of the filling and on the number of Bessel coordinates. -/

attribute [-simp] Fintype.card_pi

open Space Fintype Matrix Grading ProbabilityTheory

/-- Last step of the seesaw: a linear map R (restriction to Y_m) such that equality of the chains
through
R gives ι = B^Ψ, and each matrix coefficient of ψ, paired with a form x on Y_m, is a constant times
⟨x, Rψ⟩. -/
lemma Data.exists_last_stage_map {P} (D : Data P) {M} e : ∃ R : D.Stage M →ₗ[ℂ] _,
  (∀ {ϑ Ψ y} {φ : D.Column}, liftChainY ϑ M y = R (chainComb ϑ Ψ D.translateDatum M φ) → ι ϑ y =
  Bμ ϑ Ψ φ) ∧ ∀ t, ∃ C, ∀ x {ψ} {F : _ → ℂ}, (∀ k, F ((D.lastGrading e).inclX k) =
  algFormCoeff 1 t ψ (.blockEmb (e := .refl _) Sum.elim_one_one.symm (k, 1))) →
  (D.lastGrading e).ratBessel.qms[F * star x.1] = C * inner ℂ x (R ψ) := by
  obtain ⟨rfl, ⟨s⟩, w⟩ := e, D.isStd_spaceY, D.isHCParam_Y
  refine ⟨_ ∘ₗ D.restrictToY, (toAlgForm _ w).eq_symm_apply.1, fun t ↦
    (integral_algFormCoeff_blockEmb _ ?_ D.branching.2.2.2 t _).imp' (· * card _ * ∏ τ, _) fun C H x
    ψ F e ↦ have k := ofAlgForm_toAlgForm w x ▸
      star_ofAlgForm s; congr(∫ g, $((mul_comm ..).trans (congrArg _ ?_)) ∂$(?_)).trans
      ((H ψ _ 1 _ (Kf ..) x.2.conj.1 k).trans (congr(_ * $(integral_mul_eq_classIntegral w (Kf ..)
    x.2.conj.1 _ k)).trans
    (by simp [restrictToY]; field_simp [Finset.prod_ne_zero_iff]; rfl)).symm)⟩
  any_goals convert e (.reindex D.lastIndexEquiv (s ▸ rfl) g) <;> [apply (D.spaceY
    _).isEmbedding_ratCoordMatrix.2; apply G.ext_mat]
  repeat simp [inf_eq_left.2, LE.le, mem_besselGroup_iff, ← ext_iff, lastGrading,
    G.blockEmb, ↓ratCoordMatrix_inclX, ratCoordMatrix_eq, *]

open Nat Finset Real

namespace Data

variable {P} (D : Data P)

lemma card_besselCoord_mul_factorial_le : Fintype.card D.filling.BesselCoord * (D.k - 1)! ^ D.f ≤
  ((√√D.b ^ 5) ^ D.k) ^ D.f := by
  grw [Fintype.card_pi, prod_le_pow_card _ _ ((D.k + D.a) ^ D.k) fun v _ ↦ ?_, sub_le,
    factorial_le_pow]; simp [← mul_pow]; gcongr; use D.le_of_hasLogBound
  obtain ⟨_, A, h, ⟨⟩⟩ := (D.filling_fits.1 v).2
  grw [A.square_of_invertible _ ‹_› h,
    ← card_eq_of_equiv_fintype (schur_one_row_eq_symPowMatrix (a := D.κ v 1) (.refl _)
    ..).choose.symm, card_finsuppAntidiag_nat_eq_choose, sub_le, ← choose_symm_add, choose_le_pow]
  gcongr; all_goals grind [card_X₀, D.le_m, κ]

lemma rowParameter_sub_mem v {i l} (h : i < l) :
  (D.rowParameter v i - D.rowParameter v l : ℝ) ∈ Set.Icc 1 ↑(D.w (l + 2 - D.k) v) :=
  by simp; norm_cast; grind [D.varsigma_strictAnti v h, rowParameter]

local grind_pattern rowParameter_sub_mem => D.rowParameter v i, D.rowParameter v l

/-- With deg the degree `Filling.besselDegree` of `Data.filling` and w = `Data.nominalWeight`, the
number log deg + f Σ_{k−1 ≤ l < r} log l! lies between m(k−1) Σ_v log w(v) and mr Σ_v (log w(v) +
1/x), v over the f infinite places. -/
lemma log_filling_besselDegree_mem_Icc : log D.filling.besselDegree + D.f * ∑ l ∈ Ico (D.k - 1) D.r,
  .log l ! ∈ Set.Icc (∑ v, D.m * ((D.k - 1) * log (D.nominalWeight v))) (∑ v,
  D.m * (D.r * (log (D.nominalWeight v) + D.x⁻¹))) := by
  rw [(?_ : D.filling.besselDegree = exp (∑ v, ∑ l ∈ Ico (D.k - 1) D.r,
    (∑ i ∈ range l, log (D.rowParameter v i - D.rowParameter v l) - .log l !)))]
  · simp; constructor <;> gcongr
    grw [← @range_mono (D.k - 1),
      ← (D.nominalWeight_le_w_sub 0 ‹_›).trans (c := _ - _)] <;> norm_cast
    any_goals grw [(rowParameter_sub_mem ..).2, @range_mono _ D.r, log_w_le]
    any_goals simp [(by grind : D.r - (D.k - 1) = D.m), HasLogBound.pos D]
    all_goals grind [log_nonneg, rowParameter]
  push_cast [Filling.besselDegree, (D.filling_fits.1 _).1, ↓card_rowIndex, exp_sum, exp_sub,
    weylDimensionPoly, ↓paramW_lt_iff, paramW]; congr!
  simp [prod_comm, prod_filter, reindex_equiv D.basisNumber.symm, prod_fin_eq_prod_range,
    ← mem_range, ← prod_div_distrib]
  apply prod_congr_of_eq_on_inter
  field_simp; norm_cast; simp [← prod_range_add_one_eq_factorial]
  all_goals grind [rowParameter, prod_range_reflect, Finset.prod_congr, exp_log, cast_pos]
