/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualMomentOrderArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scalar order arithmetic and leading-one asymptotic for the original moment ceiling. -/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact scalar order arithmetic for the actual moment endpoint. -/

namespace ActualKScalarSource

noncomputable section

open Filter Topology Real

variable (C alpha D : ℝ)

private def factorial10 : ℝ := (Nat.factorial 10 : ℝ)

def B : ℝ := C * (1 + factorial10 * (2 / alpha) ^ (10 : ℕ))

def d0 : ℝ := Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)

def M : ℝ := Real.exp (D / 2)

def beta : ℝ :=
  M D * (1 + C * (Real.exp (-alpha * (D / 4) ^ (1 / 10 : ℝ)) +
    Real.exp (-D / 4))) + D + B C alpha

def curvature : ℝ :=
  ((9 + 4 * C + 2 * B C alpha) * M D + D + 3) / 4

def N : ℕ := Nat.ceil (max 1 (max (D * Real.sqrt (curvature C alpha D) / 2)
  ((5 * D / 4) * Real.exp (beta C alpha D + d0 + 2))))

def delta (D : ℝ) (q : ℕ) : ℝ := D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))

theorem B_ge_C (hC : 1 ≤ C) : C ≤ B C alpha := by
  have h : 0 ≤ factorial10 * (2 / alpha) ^ (10 : ℕ) := by
    unfold factorial10
    positivity
  unfold B
  nlinarith

theorem B_ge_one (hC : 1 ≤ C) : 1 ≤ B C alpha :=
  hC.trans (B_ge_C C alpha hC)

theorem one_le_M (hD : 0 < D) : 1 ≤ M D := by
  exact Real.one_le_exp (by positivity)

theorem base_lt_beta (hC : 1 ≤ C) : M D + D + B C alpha < beta C alpha D := by
  have hm : 0 < M D := Real.exp_pos _
  have he : 0 < C * (Real.exp (-alpha * (D / 4) ^ (1 / 10 : ℝ)) +
      Real.exp (-D / 4)) := mul_pos (by linarith) (add_pos (Real.exp_pos _) (Real.exp_pos _))
  unfold beta
  nlinarith [mul_pos hm he]

theorem two_le_beta (hC : 1 ≤ C) (hD : 0 < D) : 2 ≤ beta C alpha D := by
  have := base_lt_beta C alpha D hC
  have := B_ge_one C alpha hC
  have := one_le_M D hD
  linarith

theorem d0_nonneg : 0 ≤ d0 := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have hl := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 5 by norm_num)
  have hp : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 6) hp
  norm_num at hl
  unfold d0
  linarith

theorem curvature_pos (hC : 1 ≤ C) (hD : 0 < D) : 0 < curvature C alpha D := by
  have := B_ge_one C alpha hC
  have : 0 < M D := Real.exp_pos _
  unfold curvature
  positivity

theorem curvature_lt_two_beta_sq (hC : 1 ≤ C) (hD : 0 < D) :
    curvature C alpha D < 2 * (beta C alpha D) ^ 2 := by
  have hB := B_ge_one C alpha hC
  have hBC := B_ge_C C alpha hC
  have hM := one_le_M D hD
  have hbeta := base_lt_beta C alpha D hC
  have hS : 0 < M D + D + B C alpha := by linarith
  have hsq : (M D + D + B C alpha) ^ 2 < (beta C alpha D) ^ 2 := by
    nlinarith
  have h1 : 0 < M D * (8 * M D + 10 * B C alpha - 9) := by
    apply mul_pos <;> linarith
  have h2 : 0 ≤ 4 * M D * (B C alpha - C) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hBC)
  have h3 : 0 < 8 * (B C alpha) ^ 2 - 3 := by nlinarith
  have h4 : 0 ≤ D * (16 * M D - 1) := mul_nonneg hD.le (by linarith)
  have h5 : 0 ≤ 16 * B C alpha * D := by positivity
  have hexpand :
      8 * (M D + D + B C alpha) ^ 2 -
          ((9 + 4 * C + 2 * B C alpha) * M D + D + 3) =
        M D * (8 * M D + 10 * B C alpha - 9) +
          4 * M D * (B C alpha - C) + (8 * (B C alpha) ^ 2 - 3) +
          D * (16 * M D - 1) + 8 * D ^ 2 + 16 * B C alpha * D := by ring
  unfold curvature
  nlinarith [sq_nonneg D]

theorem scalar_facts (hC : 1 ≤ C) (hD : 0 < D) :
    C ≤ B C alpha ∧ 1 ≤ B C alpha ∧ 1 ≤ M D ∧ 2 ≤ beta C alpha D ∧
      0 ≤ d0 ∧ 0 < curvature C alpha D ∧
      curvature C alpha D < 2 * (beta C alpha D) ^ 2 :=
  ⟨B_ge_C C alpha hC, B_ge_one C alpha hC, one_le_M D hD,
    two_le_beta C alpha D hC hD, d0_nonneg, curvature_pos C alpha D hC hD,
    curvature_lt_two_beta_sq C alpha D hC hD⟩

theorem eight_beta_le_exp (hC : 1 ≤ C) (hD : 0 < D) :
    8 * beta C alpha D ≤ Real.exp (beta C alpha D + d0 + 2) := by
  have hb := two_le_beta C alpha D hC hD
  have he := Real.two_mul_le_exp (x := beta C alpha D)
  have he2 := Real.two_mul_le_exp (x := (2 : ℝ))
  have hd : Real.exp 2 ≤ Real.exp (d0 + 2) := Real.exp_le_exp.mpr (by
    linarith [d0_nonneg])
  have hp := mul_le_mul he (show 4 ≤ Real.exp (d0 + 2) by linarith)
    (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_pos _).le
  rw [show beta C alpha D + d0 + 2 = beta C alpha D + (d0 + 2) by ring,
    Real.exp_add]
  nlinarith

theorem third_term_le_N :
    (5 * D / 4) * Real.exp (beta C alpha D + d0 + 2) ≤ (N C alpha D : ℝ) := by
  exact (le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))

theorem one_le_N : 1 ≤ N C alpha D := by
  apply Nat.one_le_ceil_iff.mpr
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)

theorem ten_D_beta_le_N (hC : 1 ≤ C) (hD : 0 < D) :
    10 * D * beta C alpha D ≤ (N C alpha D : ℝ) := by
  have he := eight_beta_le_exp C alpha D hC hD
  have h := mul_le_mul_of_nonneg_left he (show 0 ≤ 5 * D / 4 by positivity)
  have hN := third_term_le_N C alpha D
  nlinarith

theorem log_five_fourths : (1 : ℝ) / 5 ≤ Real.log (5 / 4) := by
  have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  norm_num at h ⊢
  linarith

theorem q_log_lower (hD : 0 < D) :
    beta C alpha D + d0 + 2 + Real.log (5 / 4) ≤
      Real.log ((N C alpha D : ℝ) / D) := by
  have ht : (5 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2) ≤
      (N C alpha D : ℝ) / D := by
    apply (le_div_iff₀ hD).mpr
    nlinarith [third_term_le_N C alpha D]
  have hl := Real.log_le_log (by positivity :
    0 < (5 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2)) ht
  rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hl
  linarith

theorem q_delta_bound (hC : 1 ≤ C) (hD : 0 < D) :
    delta D (N C alpha D) * curvature C alpha D ≤ (1 : ℝ) / 200 := by
  have hb := two_le_beta C alpha D hC hD
  have hN := ten_D_beta_le_N C alpha D hC hD
  have hq : 0 < (N C alpha D : ℝ) := by
    exact_mod_cast (show 0 < N C alpha D from lt_of_lt_of_le Nat.zero_lt_one (one_le_N C alpha D))
  have hs : (10 * D * beta C alpha D) ^ 2 ≤ (N C alpha D : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hq.le).2 hN
  have hc := mul_le_mul_of_nonneg_left
    (curvature_lt_two_beta_sq C alpha D hC hD).le (sq_nonneg D)
  have hd : 0 < 4 * (N C alpha D : ℝ) * ((N C alpha D : ℝ) + 1) := by positivity
  unfold delta
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  nlinarith

theorem q_scalar_bounds (hC : 1 ≤ C) (hD : 0 < D) :
    1 ≤ N C alpha D ∧
      (8 : ℝ) ≤ (N C alpha D : ℝ) / D ∧
      delta D (N C alpha D) * curvature C alpha D ≤ (1 : ℝ) / 8 ∧
      beta C alpha D + d0 + 2 + (1 : ℝ) / 5 ≤
        Real.log ((N C alpha D : ℝ) / D) := by
  refine ⟨one_le_N C alpha D, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hD).mpr
    have := ten_D_beta_le_N C alpha D hC hD
    have := two_le_beta C alpha D hC hD
    nlinarith
  · exact (q_delta_bound C alpha D hC hD).trans (by norm_num)
  · linarith [q_log_lower C alpha D hD, log_five_fourths]

theorem third_max_dominates (hC : 1 ≤ C) (hD1 : 1 ≤ D) :
    max 1 (max (D * Real.sqrt (curvature C alpha D) / 2)
      ((5 * D / 4) * Real.exp (beta C alpha D + d0 + 2))) =
      (5 * D / 4) * Real.exp (beta C alpha D + d0 + 2) := by
  have hD : 0 < D := by linarith
  have hb := two_le_beta C alpha D hC hD
  have he := eight_beta_le_exp C alpha D hC hD
  have hs : Real.sqrt (curvature C alpha D) < 2 * beta C alpha D := by
    apply (Real.sqrt_lt' (by linarith : 0 < 2 * beta C alpha D)).mpr
    nlinarith [curvature_lt_two_beta_sq C alpha D hC hD]
  have ht1 : (1 : ℝ) ≤ (5 * D / 4) * Real.exp (beta C alpha D + d0 + 2) := by
    nlinarith
  have ht2 : D * Real.sqrt (curvature C alpha D) / 2 ≤
      (5 * D / 4) * Real.exp (beta C alpha D + d0 + 2) := by
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hs.le)]
  rw [max_eq_right ht2, max_eq_right ht1]

theorem q_squeeze (hC : 1 ≤ C) (hD1 : 1 ≤ D) :
    (5 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2) ≤ (N C alpha D : ℝ) / D ∧
      (N C alpha D : ℝ) / D ≤ (9 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2) := by
  have hD : 0 < D := by linarith
  have hb := two_le_beta C alpha D hC hD
  have he := eight_beta_le_exp C alpha D hC hD
  constructor
  · apply (le_div_iff₀ hD).mpr
    nlinarith [third_term_le_N C alpha D]
  · have hceil : (N C alpha D : ℝ) <
        (5 * D / 4) * Real.exp (beta C alpha D + d0 + 2) + 1 := by
      unfold N
      rw [third_max_dominates C alpha D hC hD1]
      exact Nat.ceil_lt_add_one (by positivity)
    apply (div_le_iff₀ hD).mpr
    nlinarith

theorem q_log_squeeze (hC : 1 ≤ C) :
    ∀ᶠ D : ℝ in atTop,
      beta C alpha D + d0 + 2 + Real.log (5 / 4) ≤
        Real.log ((N C alpha D : ℝ) / D) ∧
      Real.log ((N C alpha D : ℝ) / D) ≤
        beta C alpha D + d0 + 2 + Real.log (9 / 4) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD1
  have hD : 0 < D := by linarith
  refine ⟨q_log_lower C alpha D hD, ?_⟩
  have hq : 0 < (N C alpha D : ℝ) / D := by
    have : (0 : ℝ) < (N C alpha D : ℝ) := by
      exact_mod_cast (show 0 < N C alpha D from lt_of_lt_of_le Nat.zero_lt_one (one_le_N C alpha D))
    positivity
  have hl := Real.log_le_log hq (q_squeeze C alpha D hC hD1).2
  rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hl
  linarith

theorem rpow_exp_decay (ha : 0 < alpha) :
    Tendsto (fun D : ℝ => Real.exp (-alpha * (D / 4) ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := by
  have hdiv : Tendsto (fun D : ℝ => D / 4) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).2 tendsto_id
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hdiv
  have hmul := (tendsto_const_mul_atTop_of_pos ha).2 hpow
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul

theorem linear_exp_decay :
    Tendsto (fun D : ℝ => Real.exp (-D / 4)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun D : ℝ => D / 4) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).2 tendsto_id
  simpa only [Function.comp_def, neg_div] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv

theorem D_div_M_decay : Tendsto (fun D : ℝ => D / M D) atTop (𝓝 0) := by
  have hid : (fun D : ℝ => D / M D) =
      (fun D : ℝ => D ^ (1 : ℝ) * Real.exp (-(1 / 2 : ℝ) * D)) := by
    funext D
    rw [Real.rpow_one]
    simp only [M, div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [hid]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)

theorem inv_M_decay : Tendsto (fun D : ℝ => (M D)⁻¹) atTop (𝓝 0) := by
  have hid : (fun D : ℝ => (M D)⁻¹) =
      (fun D : ℝ => D ^ (0 : ℝ) * Real.exp (-(1 / 2 : ℝ) * D)) := by
    funext D
    simp only [Real.rpow_zero, one_mul, M, ← Real.exp_neg]
    congr 1
    ring
  rw [hid]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 2) (by norm_num)

theorem shifted_beta_div_M (ha : 0 < alpha) (k : ℝ) :
    Tendsto (fun D : ℝ => (beta C alpha D + k) / M D) atTop (𝓝 1) := by
  have he := (rpow_exp_decay alpha ha).add linear_exp_decay
  have hw := he.const_mul C
  have hk := inv_M_decay.const_mul (B C alpha + k)
  have ht := (((tendsto_const_nhds (x := (1 : ℝ))).add hw).add D_div_M_decay).add hk
  simp only [add_zero, mul_zero] at ht
  convert ht using 1
  funext D
  have hm : M D ≠ 0 := ne_of_gt (Real.exp_pos _)
  unfold beta
  field_simp [hm]
  ring

theorem leading_one (hC : 1 ≤ C) (ha : 0 < alpha) :
    Tendsto (fun D : ℝ => Real.log ((N C alpha D : ℝ) / D) / M D)
      atTop (𝓝 1) := by
  have hlo := shifted_beta_div_M C alpha ha (d0 + 2 + Real.log (5 / 4))
  have hhi := shifted_beta_div_M C alpha ha (d0 + 2 + Real.log (9 / 4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [q_log_squeeze C alpha hC] with D hD
    exact (div_le_div_iff_of_pos_right (Real.exp_pos _)).mpr (by linarith [hD.1])
  · filter_upwards [q_log_squeeze C alpha hC] with D hD
    exact (div_le_div_iff_of_pos_right (Real.exp_pos _)).mpr (by linarith [hD.2])

#print axioms q_scalar_bounds
#print axioms leading_one

end
end ActualKScalarSource
