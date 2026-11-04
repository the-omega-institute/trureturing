/- GID: D5/S3/Arith/Robin/EulerLayer/EulerLayerRootSecondOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayer/EulerLayerRootSecondOrder
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The uniform strict Euler inventory has the next logarithmic root coefficient. -/

import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
The second-order continuation keeps the literal strict comparison at every real clock.
The moving second-layer cutoff is controlled by MediumPNT, the first-layer
comparison, and the third-layer envelope.
-/

namespace D5.S3.Arith.Robin.EulerLayerRootSecondOrder

open Finset Filter Asymptotics
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.Robin.EulerLayerRootCorrection
open scoped Chebyshev Topology

noncomputable section

/-- A canonical choice of the root of `x^2 log x = t log t` when it exists.
The fallback is never used by the asymptotic statements, whose thresholds are >2. -/
noncomputable def second_cutoff_root (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ x : ℝ, 1 < x ∧ x ^ 2 * Real.log x = t * Real.log t then
    Classical.choose h
  else 2

/-- Strict monotonicity supplies uniqueness without any inventory witness. -/
theorem second_cutoff_strictMono :
    StrictMonoOn (fun x : ℝ => x ^ 2 * Real.log x) (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hsq : x ^ 2 < y ^ 2 := (sq_lt_sq₀ hx0.le hy0.le).mpr hxy
  calc
    x ^ 2 * Real.log x < y ^ 2 * Real.log x :=
      mul_lt_mul_of_pos_right hsq (Real.log_pos hx)
    _ ≤ y ^ 2 * Real.log y :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hx0 hxy.le) (sq_nonneg y)

private theorem second_cutoff_root_unique {t x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (hxeq : x ^ 2 * Real.log x = t * Real.log t)
    (hyeq : y ^ 2 * Real.log y = t * Real.log t) : x = y :=
  second_cutoff_strictMono.injOn hx hy (hxeq.trans hyeq.symm)

/-- IVT and uniqueness specify the original classical choice for every `t ≥ 2`. -/
theorem second_cutoff_root_spec {t : ℝ} (ht : 2 ≤ t) :
    1 < second_cutoff_root t ∧
      Real.sqrt t < second_cutoff_root t ∧
      second_cutoff_root t < Real.sqrt (2 * t) ∧
      (second_cutoff_root t) ^ 2 * Real.log (second_cutoff_root t) =
        t * Real.log t := by
  classical
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hsqrt0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsqrt1 : 1 < Real.sqrt t :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by nlinarith)
  let f : ℝ → ℝ := fun x => x ^ 2 * Real.log x
  have hflow : f (Real.sqrt t) < t * Real.log t := by
    dsimp [f]
    rw [Real.sq_sqrt ht0.le]
    exact mul_lt_mul_of_pos_left
      (Real.log_lt_log hsqrt0 (Real.sqrt_lt_self_iff.mpr ht1)) ht0
  have hfhigh : t * Real.log t < f (Real.sqrt (2 * t)) := by
    dsimp [f]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * t),
      Real.log_sqrt (by positivity : 0 ≤ 2 * t),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht0)]
    nlinarith [mul_pos ht0 (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hfcont : ContinuousOn f (Set.Icc (Real.sqrt t) (Real.sqrt (2 * t))) := by
    exact (continuousOn_id.pow 2).mul (continuousOn_id.log (fun x hx =>
      ne_of_gt (lt_of_lt_of_le hsqrt0 hx.1)))
  obtain ⟨ρ, ⟨hρlo, hρhi⟩, hρeq⟩ :=
    intermediate_value_Ioo (Real.sqrt_le_sqrt (by linarith : t ≤ 2 * t))
      hfcont ⟨hflow, hfhigh⟩
  change ρ ^ 2 * Real.log ρ = t * Real.log t at hρeq
  have hρ1 : 1 < ρ := hsqrt1.trans hρlo
  have hexists : ∃ x : ℝ, 1 < x ∧ x ^ 2 * Real.log x = t * Real.log t :=
    ⟨ρ, hρ1, hρeq⟩
  have hchosen : 1 < second_cutoff_root t ∧
      (second_cutoff_root t) ^ 2 * Real.log (second_cutoff_root t) =
        t * Real.log t := by
    rw [second_cutoff_root, dite_eq_left hexists]
    exact Classical.choose_spec hexists
  have hchoice : second_cutoff_root t = ρ :=
    second_cutoff_root_unique hchosen.1 hρ1 hchosen.2 hρeq
  simpa only [hchoice] using (show 1 < ρ ∧ Real.sqrt t < ρ ∧
    ρ < Real.sqrt (2 * t) ∧ ρ ^ 2 * Real.log ρ = t * Real.log t from
      ⟨hρ1, hρlo, hρhi, hρeq⟩)

private theorem second_cutoff_root_atTop : Tendsto second_cutoff_root atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ Real.tendsto_sqrt_atTop
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  exact (second_cutoff_root_spec ht).2.1.le

private theorem second_cutoff_log_ratio :
    Tendsto (fun t : ℝ => Real.log (second_cutoff_root t) / Real.log t)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hsmall : Tendsto (fun t : ℝ => Real.log 2 / Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hupper : Tendsto (fun t : ℝ => (Real.log 2 / Real.log t + 1) / 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (hsmall.add_const 1).div_const 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    obtain ⟨hρ1, hρlo, hρhi, hρeq⟩ := second_cutoff_root_spec ht
    have ht0 : 0 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have h := Real.log_le_log (Real.sqrt_pos.mpr ht0) hρlo.le
    rw [Real.log_sqrt ht0.le] at h
    apply (le_div_iff₀ hlogt).mpr
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    obtain ⟨hρ1, hρlo, hρhi, hρeq⟩ := second_cutoff_root_spec ht
    have ht0 : 0 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have h := Real.log_le_log (lt_trans zero_lt_one hρ1) hρhi.le
    rw [Real.log_sqrt (by positivity : 0 ≤ 2 * t),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht0)] at h
    apply (div_le_iff₀ hlogt).mpr
    calc
      Real.log (second_cutoff_root t) ≤ (Real.log 2 + Real.log t) / 2 := h
      _ = ((Real.log 2 / Real.log t + 1) / 2) * Real.log t := by
        field_simp [ne_of_gt hlogt]

/-- The root equation, rather than the crude root bracket, determines this limit. -/
private theorem second_cutoff_root_ratio :
    Tendsto (fun t : ℝ => second_cutoff_root t / Real.sqrt t)
      atTop (𝓝 (Real.sqrt 2)) := by
  have hinv : Tendsto (fun t : ℝ =>
      (Real.log (second_cutoff_root t) / Real.log t)⁻¹) atTop (𝓝 2) := by
    simpa using second_cutoff_log_ratio.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hsq : Tendsto (fun t : ℝ => (second_cutoff_root t / Real.sqrt t) ^ 2)
      atTop (𝓝 2) := by
    apply hinv.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    obtain ⟨hρ1, hρlo, hρhi, hρeq⟩ := second_cutoff_root_spec ht
    have ht0 : 0 < t := by linarith
    have hlogρ : 0 < Real.log (second_cutoff_root t) := Real.log_pos hρ1
    rw [inv_div, div_pow, Real.sq_sqrt ht0.le]
    apply (div_eq_div_iff (ne_of_gt hlogρ) (ne_of_gt ht0)).mpr
    nlinarith only [hρeq]
  apply hsq.sqrt.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  exact Real.sqrt_sq (div_nonneg
    (lt_trans zero_lt_one (second_cutoff_root_spec ht).1).le (Real.sqrt_nonneg t))

private theorem second_cutoff_normalized_limit :
    Tendsto (fun t : ℝ => second_cutoff_root t / Real.sqrt (2 * t))
      atTop (𝓝 1) := by
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h := second_cutoff_root_ratio.div_const (Real.sqrt 2)
  rw [div_self htwo] at h
  apply h.congr'
  filter_upwards [] with t
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), div_div]
  congr 1
  ring

/-- Factoring the exact normalized equation gives the next coefficient without an ansatz. -/
private theorem second_cutoff_root_second_order :
    Tendsto (fun t : ℝ => Real.log t *
      (second_cutoff_root t / Real.sqrt t - Real.sqrt 2) +
      Real.sqrt 2 * Real.log 2 / 2) atTop (𝓝 0) := by
  let s : ℝ → ℝ := fun t => second_cutoff_root t / Real.sqrt (2 * t)
  have hs : Tendsto s atTop (𝓝 1) := second_cutoff_normalized_limit
  have hslog : Tendsto (fun t : ℝ => Real.log (s t)) atTop (𝓝 0) := by
    simpa using hs.log (by norm_num : (1 : ℝ) ≠ 0)
  have hsq : Tendsto (fun t : ℝ => (s t) ^ 2) atTop (𝓝 1) := by
    simpa using hs.pow 2
  have hrhs : Tendsto (fun t : ℝ =>
      -(s t) ^ 2 * (Real.log 2 + 2 * Real.log (s t)) / (s t + 1))
      atTop (𝓝 (-Real.log 2 / 2)) := by
    have hconst : Tendsto (fun _ : ℝ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
      tendsto_const_nhds
    convert (hsq.neg.mul (hconst.add (hslog.const_mul 2))).div
        (hs.add_const 1) (by norm_num : (1 : ℝ) + 1 ≠ 0) using 1 <;> norm_num
  have hLs : Tendsto (fun t : ℝ => Real.log t * (s t - 1))
      atTop (𝓝 (-Real.log 2 / 2)) := by
    apply hrhs.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    obtain ⟨hρ1, hρlo, hρhi, hρeq⟩ := second_cutoff_root_spec ht
    have ht0 : 0 < t := by linarith
    have hden : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
    have hspos : 0 < s t := div_pos (lt_trans zero_lt_one hρ1) hden
    have hρ : second_cutoff_root t = s t * Real.sqrt (2 * t) := by
      dsimp [s]
      rw [div_mul_cancel₀ _ (ne_of_gt hden)]
    have hρsq : (second_cutoff_root t) ^ 2 = (s t) ^ 2 * (2 * t) := by
      rw [hρ, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * t)]
    have hρlog : Real.log (second_cutoff_root t) =
        Real.log (s t) + (Real.log 2 + Real.log t) / 2 := by
      rw [hρ, Real.log_mul (ne_of_gt hspos) (ne_of_gt hden),
        Real.log_sqrt (by positivity : 0 ≤ 2 * t),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht0)]
    rw [hρsq, hρlog] at hρeq
    have hz : t * ((s t) ^ 2 *
        (Real.log t + Real.log 2 + 2 * Real.log (s t)) - Real.log t) = 0 := by
      nlinarith only [hρeq]
    have hnormalized : (s t) ^ 2 *
        (Real.log t + Real.log 2 + 2 * Real.log (s t)) = Real.log t := by
      have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt ht0)
      linarith
    have hfactor : Real.log t * (s t - 1) =
        -(s t) ^ 2 * (Real.log 2 + 2 * Real.log (s t)) / (s t + 1) := by
      apply (eq_div_iff (ne_of_gt (show 0 < s t + 1 by linarith))).mpr
      nlinarith only [hnormalized]
    exact hfactor.symm
  have h := (hLs.const_mul (Real.sqrt 2)).add_const (Real.sqrt 2 * Real.log 2 / 2)
  have hz : Real.sqrt 2 * (-Real.log 2 / 2) + Real.sqrt 2 * Real.log 2 / 2 = 0 := by
    ring
  rw [hz] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hratio : second_cutoff_root t / Real.sqrt t = Real.sqrt 2 * s t := by
    dsimp [s]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [htwo, ne_of_gt (Real.sqrt_pos.mpr ht0)]
    <;> ring
  rw [hratio]
  ring

/-- The weak PNT estimate needed at the smaller-than-root logarithmic scale. -/
private theorem theta_sub_id_log_small :
    Tendsto (fun x : ℝ => Real.log x * (Chebyshev.theta x - x) / x)
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hpnt⟩ := _root_.MediumPNT
  have hmedium_exp : Tendsto
      (fun x : ℝ => Real.log x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 : ℝ) c hc).comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        Real.tendsto_log_atTop)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul (Real.log_nonneg hx.le)]
    norm_num
  have hmedium : Tendsto
      (fun x : ℝ => Real.log x * ((Chebyshev.psi x - x) / x))
      atTop (𝓝 0) := by
    obtain ⟨C, hC⟩ := hpnt.bound
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_
      (by simpa only [mul_zero] using hmedium_exp.const_mul C)
    filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with x hCx hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hbound : |Chebyshev.psi x - x| ≤
        C * (x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) := by
      simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hx0.le
          (Real.exp_pos (-c * Real.log x ^ (1 / 10 : ℝ))).le)] using hCx
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hlog, abs_of_pos hx0]
    calc
      Real.log x * (|Chebyshev.psi x - x| / x) ≤
          Real.log x * ((C * (x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)))) / x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbound hx0.le) hlog
      _ = C * (Real.log x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) := by
        field_simp [ne_of_gt hx0]
  have hgaplog : Tendsto
      (fun x : ℝ => Real.log x * ((Chebyshev.psi x - Chebyshev.theta x) / x))
      atTop (𝓝 0) := by
    obtain ⟨C, hC⟩ := Chebyshev.isBigO_psi_sub_theta_sqrt.bound
    have hlogroot : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x)
        atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow] using
        (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine squeeze_zero' ?_ ?_
      (by simpa only [mul_zero] using hlogroot.const_mul C)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact mul_nonneg (Real.log_nonneg hx)
        (div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))
          (le_trans zero_le_one hx))
    · filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with x hCx hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
      have habs : |Chebyshev.psi x - Chebyshev.theta x| ≤ C * Real.sqrt x := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg x)] using hCx
      have hbound := (le_abs_self (Chebyshev.psi x - Chebyshev.theta x)).trans habs
      calc
        Real.log x * ((Chebyshev.psi x - Chebyshev.theta x) / x) ≤
            Real.log x * ((C * Real.sqrt x) / x) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbound hx0.le) hlog
        _ = C * (Real.log x / Real.sqrt x) := by
          rw [mul_div_assoc, Real.sqrt_div_self]
          ring
  have h := hmedium.sub hgaplog
  simp only [sub_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun x => by ring

/-- The prime-power tail after the square layer is smaller than the requested
`sqrt t / log t` scale.  This is obtained from Costa--Pereira's existing
three-term inequalities and `psi_le_const_mul_self`, rather than from the
leading root limit. -/
private theorem psi_after_sqrt_small :
    Tendsto
      (fun t : ℝ => Real.log t *
        ((Chebyshev.psi t - Chebyshev.theta t -
          Chebyshev.theta (Real.sqrt t)) / Real.sqrt t))
      atTop (𝓝 0) := by
  have hpower (r : ℝ) (hr : r < 1 / 2) :
      Tendsto (fun t : ℝ => Real.log t * (t ^ r / Real.sqrt t)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (sub_pos.mpr hr)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.sqrt_eq_rpow, Real.rpow_sub ht]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos ht r),
      ne_of_gt (Real.rpow_pos_of_pos ht (1 / 2 : ℝ))]
  have hsmall (r : ℝ) (hr : r < 1 / 2) :
      Tendsto (fun t : ℝ => Real.log t *
        (Chebyshev.psi (t ^ r) / Real.sqrt t)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_
      (by simpa only [mul_zero] using (hpower r hr).const_mul (Real.log 4 + 4))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact mul_nonneg (Real.log_nonneg ht)
        (div_nonneg (Chebyshev.psi_nonneg _) (Real.sqrt_nonneg t))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hbound := Chebyshev.psi_le_const_mul_self
        (Real.rpow_nonneg (le_trans zero_le_one ht) r)
      calc
        Real.log t * (Chebyshev.psi (t ^ r) / Real.sqrt t) ≤
            Real.log t * (((Real.log 4 + 4) * t ^ r) / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg t)) (Real.log_nonneg ht)
        _ = (Real.log 4 + 4) * (Real.log t * (t ^ r / Real.sqrt t)) := by ring
  have hroot : Tendsto
      (fun t : ℝ => Real.log t *
        ((Chebyshev.psi (Real.sqrt t) - Chebyshev.theta (Real.sqrt t)) / Real.sqrt t))
      atTop (𝓝 0) := by
    have hscale : Tendsto
        (fun t : ℝ => Real.log t * (Real.sqrt (Real.sqrt t) / Real.sqrt t))
        atTop (𝓝 0) := by
      apply (hpower (1 / 4) (by norm_num)).congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have hquarter : Real.sqrt (Real.sqrt t) = t ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
        norm_num
      rw [hquarter]
    obtain ⟨C, hC⟩ := Chebyshev.isBigO_psi_sub_theta_sqrt.bound
    refine squeeze_zero' ?_ ?_
      (by simpa only [mul_zero] using hscale.const_mul C)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact mul_nonneg (Real.log_nonneg ht)
        (div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi (Real.sqrt t)))
          (Real.sqrt_nonneg t))
    · filter_upwards [Real.tendsto_sqrt_atTop.eventually hC,
        eventually_ge_atTop (1 : ℝ)] with t hCt ht
      have habs : |Chebyshev.psi (Real.sqrt t) - Chebyshev.theta (Real.sqrt t)| ≤
          C * Real.sqrt (Real.sqrt t) := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg (Real.sqrt t))] using hCt
      have hbound :=
        (le_abs_self (Chebyshev.psi (Real.sqrt t) - Chebyshev.theta (Real.sqrt t))).trans habs
      calc
        Real.log t *
            ((Chebyshev.psi (Real.sqrt t) - Chebyshev.theta (Real.sqrt t)) / Real.sqrt t) ≤
            Real.log t * ((C * Real.sqrt (Real.sqrt t)) / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg t)) (Real.log_nonneg ht)
        _ = C * (Real.log t * (Real.sqrt (Real.sqrt t) / Real.sqrt t)) := by ring
  have hsmall13 := hsmall (1 / 3) (by norm_num)
  have hsmall15 := hsmall (1 / 5) (by norm_num)
  have hsmall17 := hsmall (1 / 7) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (hroot.add hsmall13).add hsmall17)
    (by simpa using (hroot.add hsmall13).add hsmall15)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hcp : Chebyshev.psi (Real.sqrt t) + Chebyshev.psi (t ^ (1 / 3 : ℝ)) +
        Chebyshev.psi (t ^ (1 / 7 : ℝ)) ≤ Chebyshev.psi t - Chebyshev.theta t := by
      simpa only [Real.sqrt_eq_rpow, one_div] using
        Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi (le_trans zero_le_one ht)
    have hbound : (Chebyshev.psi (Real.sqrt t) - Chebyshev.theta (Real.sqrt t)) +
        Chebyshev.psi (t ^ (1 / 3 : ℝ)) + Chebyshev.psi (t ^ (1 / 7 : ℝ)) ≤
        Chebyshev.psi t - Chebyshev.theta t - Chebyshev.theta (Real.sqrt t) := by
      linarith
    have h := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg t)) (Real.log_nonneg ht)
    simpa only [add_div, mul_add, one_div] using h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hcp : Chebyshev.psi t - Chebyshev.theta t ≤
        Chebyshev.psi (Real.sqrt t) + Chebyshev.psi (t ^ (1 / 3 : ℝ)) +
          Chebyshev.psi (t ^ (1 / 5 : ℝ)) := by
      simpa only [Real.sqrt_eq_rpow, one_div] using
        Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t
    have hbound : Chebyshev.psi t - Chebyshev.theta t - Chebyshev.theta (Real.sqrt t) ≤
        (Chebyshev.psi (Real.sqrt t) - Chebyshev.theta (Real.sqrt t)) +
          Chebyshev.psi (t ^ (1 / 3 : ℝ)) + Chebyshev.psi (t ^ (1 / 5 : ℝ)) := by
      linarith
    have h := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg t)) (Real.log_nonneg ht)
    simpa only [add_div, mul_add, one_div] using h

/-- Exact second-layer bracket at a moving real cutoff. -/
private theorem second_layer_cutoff_bracket :
    ∀ᶠ t : ℝ in atTop, ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      ∃ ρ : ℝ,
        Real.sqrt t < ρ ∧ ρ < Real.sqrt (2 * t) ∧
        ρ ^ 2 * Real.log ρ = t * Real.log t ∧
        Chebyshev.theta (ρ - 1) ≤ strict_inventory_second_layer_mass U ∧
        strict_inventory_second_layer_mass U ≤ Chebyshev.theta ρ := by
  classical
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht U hU hstrict
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hprice : 0 < 1 / (t * Real.log t) := one_div_pos.mpr (mul_pos ht0 hlogt)
  let ρ := second_cutoff_root t
  have hspec := second_cutoff_root_spec ht
  change 1 < ρ ∧ Real.sqrt t < ρ ∧ ρ < Real.sqrt (2 * t) ∧
    ρ ^ 2 * Real.log ρ = t * Real.log t at hspec
  obtain ⟨hρ1, hρlo, hρhi, hρeq⟩ := hspec
  have hρ0 : 0 < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ1
  -- These are bounds for the literal marginal, not a replacement activation cut.
  have hmarginal (q : ℕ) (hq : q.Prime) :
      1 / (((q : ℝ) ^ 2 + q + 1) * Real.log q) ≤
        D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal q 2 ∧
      D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal q 2 <
        1 / (((q : ℝ) ^ 2 + q) * Real.log q) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
    have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
    let A : ℝ := (q : ℝ) ^ 2 + q
    have hA : 0 < A := by dsimp [A]; positivity
    have hA1 : 0 < A + 1 := by linarith
    have harg1 : 1 < 1 + 1 / A := by linarith [one_div_pos.mpr hA]
    have harg0 : 0 < 1 + 1 / A := by linarith
    have hden : 1 - (q : ℝ)⁻¹ ^ 2 ≠ 0 := by
      have hi : (q : ℝ)⁻¹ < 1 := (inv_lt_one₀ hq0).mpr hq1
      exact ne_of_gt (sub_pos.mpr
        (pow_lt_one₀ (inv_nonneg.mpr hq0.le) hi (by norm_num : (2 : ℕ) ≠ 0)))
    have hratio : (1 - (q : ℝ)⁻¹ ^ (2 + 1)) / (1 - (q : ℝ)⁻¹ ^ 2) =
        1 + 1 / A := by
      apply (div_eq_iff hden).mpr
      dsimp [A]
      field_simp [ne_of_gt hq0, ne_of_gt hA]
      ring
    have hlogL : 1 / (A + 1) ≤ Real.log (1 + 1 / A) := by
      have hid : 1 - (1 + 1 / A)⁻¹ = 1 / (A + 1) := by
        field_simp [ne_of_gt hA, ne_of_gt hA1]
        ring
      simpa only [hid] using Real.one_sub_inv_le_log_of_pos harg0
    have hlogU : Real.log (1 + 1 / A) < 1 / A := by
      have h := Real.log_lt_sub_one_of_pos harg0 (ne_of_gt harg1)
      linarith
    change 1 / ((A + 1) * Real.log q) ≤ _ ∧ _ < 1 / (A * Real.log q)
    unfold D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal
    rw [hratio]
    constructor
    · calc
        _ = (1 / (A + 1)) / Real.log q := by rw [div_div]
        _ ≤ _ := (div_le_div_iff_of_pos_right hlogq).mpr hlogL
    · calc
        _ < (1 / A) / Real.log q := (div_lt_div_iff_of_pos_right hlogq).mpr hlogU
        _ = _ := by rw [div_div]
  have hactive_lower : ∀ q : ℕ, q.Prime → (q : ℝ) ≤ ρ - 1 →
      2 ≤ U.factorization q := by
    intro q hq hqρ
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlogq : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast hq.one_lt)
    have hsq : ((q : ℝ) + 1) ^ 2 ≤ ρ ^ 2 :=
      (sq_le_sq₀ (by positivity : 0 ≤ (q : ℝ) + 1) hρ0.le).mpr (by linarith)
    have hpoly : (q : ℝ) ^ 2 + q + 1 < ρ ^ 2 := by nlinarith
    have hlogqρ : Real.log (q : ℝ) ≤ Real.log ρ :=
      Real.log_le_log hq0 (by linarith)
    have hmul : ((q : ℝ) ^ 2 + q + 1) * Real.log q < t * Real.log t := by
      calc
        _ ≤ ((q : ℝ) ^ 2 + q + 1) * Real.log ρ :=
          mul_le_mul_of_nonneg_left hlogqρ (by positivity)
        _ < ρ ^ 2 * Real.log ρ := mul_lt_mul_of_pos_right hpoly hlogρ
        _ = _ := hρeq
    have hgain : 1 / (t * Real.log t) <
        D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal q 2 :=
      (one_div_lt_one_div_of_lt (mul_pos (by positivity) hlogq) hmul).trans_le
        (hmarginal q hq).1
    have hmem : 2 ∈ Set.Icc 1 (optimalLayerCount (1 / (t * Real.log t)) q) := by
      rw [← positive_layers_eq_count_interval hprice hq]
      exact ⟨by norm_num, hq, hgain⟩
    rw [hstrict q hq]
    exact hmem.2
  have hactive_upper : ∀ q : ℕ, q.Prime → 2 ≤ U.factorization q →
      (q : ℝ) < ρ := by
    intro q hq hq2
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hmem : 2 ∈ Set.Icc 1 (optimalLayerCount (1 / (t * Real.log t)) q) :=
      ⟨by norm_num, by rwa [← hstrict q hq]⟩
    rw [← positive_layers_eq_count_interval hprice hq] at hmem
    have hgain := hmem.2.2
    by_contra hn
    have hρq : ρ ≤ (q : ℝ) := le_of_not_gt hn
    have hsq : ρ ^ 2 ≤ (q : ℝ) ^ 2 := (sq_le_sq₀ hρ0.le hq0.le).mpr hρq
    have hpoly : ρ ^ 2 < (q : ℝ) ^ 2 + q := by linarith
    have hlogρq : Real.log ρ ≤ Real.log (q : ℝ) := Real.log_le_log hρ0 hρq
    have hmul : t * Real.log t < ((q : ℝ) ^ 2 + q) * Real.log q := by
      calc
        _ = ρ ^ 2 * Real.log ρ := hρeq.symm
        _ < ((q : ℝ) ^ 2 + q) * Real.log ρ :=
          mul_lt_mul_of_pos_right hpoly hlogρ
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogρq (by positivity)
    have hinactive :
        D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal q 2 <
          1 / (t * Real.log t) :=
      (hmarginal q hq).2.trans (one_div_lt_one_div_of_lt (mul_pos ht0 hlogt) hmul)
    exact (not_lt_of_ge hinactive.le) hgain
  have hlower : Chebyshev.theta (ρ - 1) ≤ strict_inventory_second_layer_mass U := by
    unfold strict_inventory_second_layer_mass
    rw [Chebyshev.theta_eq_sum_primesLE]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hqP
      obtain ⟨hqρ, hq⟩ := Nat.mem_primesLE.mp hqP
      have hqρ' : (q : ℝ) ≤ ρ - 1 :=
        (Nat.le_floor_iff (by linarith : 0 ≤ ρ - 1)).mp hqρ
      have hq2 := hactive_lower q hq hqρ'
      refine Finset.mem_filter.mpr ⟨?_, hq2⟩
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    · intro q _ _
      exact Real.log_natCast_nonneg q
  have hupper : strict_inventory_second_layer_mass U ≤ Chebyshev.theta ρ := by
    unfold strict_inventory_second_layer_mass
    rw [Chebyshev.theta_eq_sum_primesLE]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hqS
      obtain ⟨hqU, hq2⟩ := Finset.mem_filter.mp hqS
      have hq := Nat.prime_of_mem_primeFactors hqU
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff hρ0.le).mpr (hactive_upper q hq hq2).le, hq⟩
    · intro q _ _
      exact Real.log_natCast_nonneg q
  exact ⟨ρ, hρlo, hρhi, hρeq, hlower, hupper⟩

/-- The explicit third-layer envelope is still negligible after multiplication
by `log t`, uniformly before choosing the strict inventory. -/
private theorem strict_inventory_third_layer_log_vanishing :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      |Real.log t * (strict_inventory_third_layer_mass U / Real.sqrt t)| < ε := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hrootcoeff : (3 : ℝ) ^ (1 / 3 : ℝ) ≤ 3 := by
    calc
      (3 : ℝ) ^ (1 / 3 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := by norm_num
  have hlogpow : Tendsto
      (fun t : ℝ => Real.log t ^ 2 / t ^ (1 / 6 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero
  have hscale : ∀ᶠ t : ℝ in atTop,
      Real.log t *
        ((((3 * t) ^ (1 / 3 : ℝ) + 1) *
          Real.log (t * Real.log t / Real.log 2)) / Real.sqrt t) ≤
        12 * (Real.log t ^ 2 / t ^ (1 / 6 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hargpos : 0 < t * Real.log t / Real.log 2 :=
      div_pos (mul_pos ht0 hlogt) hlog2
    have hargle : t * Real.log t / Real.log 2 ≤ 2 * t ^ 2 := by
      apply (div_le_iff₀ hlog2).mpr
      have hleft := mul_le_mul_of_nonneg_left (Real.log_le_self ht0.le) ht0.le
      have hright := mul_le_mul_of_nonneg_left hlog2lower
        (show 0 ≤ 2 * t ^ 2 by positivity)
      nlinarith only [hleft, hright]
    have hlogarg : Real.log (t * Real.log t / Real.log 2) ≤ 3 * Real.log t := by
      calc
        _ ≤ Real.log (2 * t ^ 2) := Real.log_le_log hargpos hargle
        _ = Real.log 2 + 2 * Real.log t := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          norm_num
        _ ≤ 3 * Real.log t := by
          linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht]
    have hroot : (3 * t) ^ (1 / 3 : ℝ) + 1 ≤ 4 * t ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) ht0.le]
      have htroot : 1 ≤ t ^ (1 / 3 : ℝ) :=
        Real.one_le_rpow (by linarith) (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right hrootcoeff
        (show 0 ≤ t ^ (1 / 3 : ℝ) by positivity)
      linarith only [hmul, htroot]
    have hnum : ((3 * t) ^ (1 / 3 : ℝ) + 1) *
        Real.log (t * Real.log t / Real.log 2) ≤
        12 * t ^ (1 / 3 : ℝ) * Real.log t := by
      calc
        _ ≤ ((3 * t) ^ (1 / 3 : ℝ) + 1) * (3 * Real.log t) :=
          mul_le_mul_of_nonneg_left hlogarg (by positivity)
        _ ≤ (4 * t ^ (1 / 3 : ℝ)) * (3 * Real.log t) :=
          mul_le_mul_of_nonneg_right hroot (by positivity)
        _ = 12 * t ^ (1 / 3 : ℝ) * Real.log t := by ring
    have hpower : Real.sqrt t = t ^ (1 / 3 : ℝ) * t ^ (1 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
      norm_num
    calc
      _ ≤ Real.log t * ((12 * t ^ (1 / 3 : ℝ) * Real.log t) / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hnum hsqrt.le) hlogt.le
      _ = 12 * (Real.log t ^ 2 / t ^ (1 / 6 : ℝ)) := by
        rw [hpower]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos ht0 (1 / 3 : ℝ)),
          ne_of_gt (Real.rpow_pos_of_pos ht0 (1 / 6 : ℝ))]
  have hlimit : Tendsto
      (fun t : ℝ => 12 * (Real.log t ^ 2 / t ^ (1 / 6 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlogpow.const_mul 12
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hlimit.eventually_lt_const hε).and hscale)
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro t ht U hU hstrict
  have ht2 : 2 ≤ t := (le_max_right T 2).trans ht
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hmass_nonneg : 0 ≤ strict_inventory_third_layer_mass U := by
    unfold strict_inventory_third_layer_mass
    exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q)
  rw [abs_of_nonneg (mul_nonneg hlogt.le (div_nonneg hmass_nonneg hsqrt.le))]
  have hweighted := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right
      (strict_inventory_third_layer_bound ht2 hU hstrict) hsqrt.le) hlogt.le
  have hT' := hT t ((le_max_left T 2).trans ht)
  exact hweighted.trans_lt (hT'.2.trans_lt hT'.1)

/-- Transport the logarithmic theta error along a moving root-scale endpoint. -/
private theorem theta_endpoint_second_order (x : ℝ → ℝ)
    (hx : Tendsto x atTop atTop)
    (hratio : Tendsto (fun t : ℝ => x t / Real.sqrt t) atTop (𝓝 (Real.sqrt 2)))
    (hsecond : Tendsto (fun t : ℝ => Real.log t *
      (x t / Real.sqrt t - Real.sqrt 2) + Real.sqrt 2 * Real.log 2 / 2)
        atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => Real.log t *
      (Chebyshev.theta (x t) / Real.sqrt t - Real.sqrt 2) +
      Real.sqrt 2 * Real.log 2 / 2) atTop (𝓝 0) := by
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsmall : Tendsto (fun t : ℝ => Real.log (x t / Real.sqrt t) / Real.log t)
      atTop (𝓝 0) := (hratio.log htwo).div_atTop Real.tendsto_log_atTop
  have hlogratio : Tendsto (fun t : ℝ => Real.log (x t) / Real.log t)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := hsmall.add_const (1 / 2 : ℝ)
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ), hx.eventually_gt_atTop (1 : ℝ)]
      with t ht hxt
    have ht0 : 0 < t := by linarith
    rw [Real.log_div (ne_of_gt (lt_trans zero_lt_one hxt))
      (ne_of_gt (Real.sqrt_pos.mpr ht0)), Real.log_sqrt ht0.le]
    field_simp [ne_of_gt (Real.log_pos (show 1 < t by linarith))]
    ring
  have hinv : Tendsto (fun t : ℝ => Real.log t / Real.log (x t)) atTop (𝓝 2) := by
    simpa only [inv_div, div_one] using
      hlogratio.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hprod := ((theta_sub_id_log_small.comp hx).mul hinv).mul hratio
  simp only [zero_mul, Function.comp_def] at hprod
  have herror : Tendsto (fun t : ℝ =>
      Real.log t * (Chebyshev.theta (x t) - x t) / Real.sqrt t) atTop (𝓝 0) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ), hx.eventually_gt_atTop (1 : ℝ)]
      with t ht hxt
    have ht0 : 0 < t := by linarith
    field_simp [ne_of_gt (lt_trans zero_lt_one hxt), ne_of_gt (Real.log_pos hxt),
      ne_of_gt (Real.sqrt_pos.mpr ht0)]
  have h := herror.add hsecond
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with t
  ring

/-- The second-layer mass has the exact next logarithmic coefficient. -/
private theorem strict_inventory_second_layer_second_order :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      |Real.log t *
          (strict_inventory_second_layer_mass U / Real.sqrt t - Real.sqrt 2) +
        Real.sqrt 2 * Real.log 2 / 2| < ε := by
  intro ε hε
  have hlogsmall : Tendsto (fun t : ℝ => Real.log t / Real.sqrt t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have honeroot : Tendsto (fun t : ℝ => 1 / Real.sqrt t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hminus_atTop : Tendsto (fun t : ℝ => second_cutoff_root t - 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [second_cutoff_root_atTop.eventually_ge_atTop (b + 1)] with t ht
    linarith
  have hminus_ratio : Tendsto (fun t : ℝ => (second_cutoff_root t - 1) / Real.sqrt t)
      atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [sub_zero, ← sub_div] using second_cutoff_root_ratio.sub honeroot
  have hminus_second : Tendsto (fun t : ℝ => Real.log t *
      ((second_cutoff_root t - 1) / Real.sqrt t - Real.sqrt 2) +
      Real.sqrt 2 * Real.log 2 / 2) atTop (𝓝 0) := by
    have h := second_cutoff_root_second_order.sub hlogsmall
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [] with t
    ring
  have htheta_upper := theta_endpoint_second_order second_cutoff_root
    second_cutoff_root_atTop second_cutoff_root_ratio second_cutoff_root_second_order
  have htheta_lower := theta_endpoint_second_order (fun t => second_cutoff_root t - 1)
    hminus_atTop hminus_ratio hminus_second
  -- Take bounds depending only on the real clock before introducing any inventory.
  obtain ⟨Tθ, hTθ⟩ := eventually_atTop.mp
    ((htheta_lower.eventually_const_lt (show -ε < 0 by linarith)).and
      (htheta_upper.eventually_lt_const hε))
  obtain ⟨Tb, hTb⟩ := eventually_atTop.mp second_layer_cutoff_bracket
  let T := max (max Tθ Tb) 2
  refine ⟨T, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro t ht U hU hstrict
  have ht2 : 2 ≤ t := (le_max_right (max Tθ Tb) 2).trans ht
  have htθ : Tθ ≤ t :=
    (le_max_left Tθ Tb).trans ((le_max_left (max Tθ Tb) 2).trans ht)
  have htb : Tb ≤ t :=
    (le_max_right Tθ Tb).trans ((le_max_left (max Tθ Tb) 2).trans ht)
  obtain ⟨ρ, hρlo, hρhi, hρeq, hlower, hupper⟩ := hTb t htb U hU hstrict
  obtain ⟨hroot1, hrootlo, hroothi, hrooteq⟩ := second_cutoff_root_spec ht2
  have hsqrt1 : 1 < Real.sqrt t :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by nlinarith)
  have hρ : ρ = second_cutoff_root t :=
    second_cutoff_root_unique (hsqrt1.trans hρlo) hroot1 hρeq hrooteq
  rw [hρ] at hlower hupper
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlo := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hlower (Real.sqrt_nonneg t)) hlogt.le
  have hup := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hupper (Real.sqrt_nonneg t)) hlogt.le
  obtain ⟨hloε, hupε⟩ := hTθ t htθ
  apply abs_lt.mpr
  constructor <;> linarith

/-- Uniform next-order strict Euler inventory law, with all real clocks,
all prime binders, and every positive natural witness retained. -/
theorem strict_inventory_root_second_order :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      |Real.log t *
          ((Real.log U - Chebyshev.psi t) / Real.sqrt t - (Real.sqrt 2 - 1)) +
        Real.sqrt 2 * Real.log 2 / 2| < ε := by
  classical
  intro ε hε
  have hη : 0 < ε / 6 := by linarith
  obtain ⟨T2, hT2, hsecond⟩ := strict_inventory_second_layer_second_order (ε / 6) hη
  obtain ⟨T3, hT3, hthird⟩ := strict_inventory_third_layer_log_vanishing (ε / 6) hη
  have hfirstlog : Tendsto (fun t : ℝ => Real.log t * (Real.log t / Real.sqrt t))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_two, pow_two, mul_div_assoc, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hthetaSqrt : Tendsto
      (fun t : ℝ => Real.log t *
        ((Chebyshev.theta (Real.sqrt t) - Real.sqrt t) / Real.sqrt t))
      atTop (𝓝 0) := by
    have h := (theta_sub_id_log_small.comp Real.tendsto_sqrt_atTop).const_mul (2 : ℝ)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    dsimp only [Function.comp_def]
    rw [Real.log_sqrt ht]
    ring
  have habs {f : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
      ∀ᶠ t : ℝ in atTop, |f t| < ε / 6 := by
    have hlo := (tendsto_order.mp hf).1 (-(ε / 6)) (by linarith)
    have hhi := (tendsto_order.mp hf).2 (ε / 6) hη
    filter_upwards [hlo, hhi] with t hl hu
    exact abs_lt.mpr ⟨hl, hu⟩
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp
    ((habs hfirstlog).and ((habs hthetaSqrt).and (habs psi_after_sqrt_small)))
  let T := max (max T2 T3) (max Ta 2)
  refine ⟨T, ?_, ?_⟩
  · exact hT2.trans_le
      ((le_max_left T2 T3).trans (le_max_left (max T2 T3) (max Ta 2)))
  · intro t ht U hU hstrict
    have htbase : max Ta 2 ≤ t := (le_max_right (max T2 T3) (max Ta 2)).trans ht
    have ht2 : 2 ≤ t := (le_max_right Ta 2).trans htbase
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hsecond' := hsecond t
      ((le_max_left T2 T3).trans ((le_max_left (max T2 T3) (max Ta 2)).trans ht))
      U hU hstrict
    have hthird' := hthird t
      ((le_max_right T2 T3).trans ((le_max_left (max T2 T3) (max Ta 2)).trans ht))
      U hU hstrict
    have hsmall := hTa t ((le_max_left Ta 2).trans htbase)
    have hfirst := EulerLayerInventoryGrowth.first_layer_comparison ht2 hU hstrict
    have hfirst_abs : |(∑ q ∈ U.primeFactors, Real.log q) - Chebyshev.theta t| ≤
        Real.log t := by
      apply abs_le.mpr
      constructor <;> linarith [hfirst.1, hfirst.2]
    have hfirst_weight :
        |Real.log t * (((∑ q ∈ U.primeFactors, Real.log q) - Chebyshev.theta t) /
          Real.sqrt t)| ≤ Real.log t * (Real.log t / Real.sqrt t) := by
      rw [abs_mul, abs_div, abs_of_nonneg hlogt.le, abs_of_pos hsqrt]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hfirst_abs hsqrt.le) hlogt.le
    have hfirst' :
        |Real.log t * (((∑ q ∈ U.primeFactors, Real.log q) - Chebyshev.theta t) /
          Real.sqrt t)| < ε / 6 :=
      hfirst_weight.trans_lt ((le_abs_self _).trans_lt hsmall.1)
    have hsplit := log_inventory_split hU
    have htelescope :
        Real.log t *
            ((Real.log U - Chebyshev.psi t) / Real.sqrt t - (Real.sqrt 2 - 1)) +
          Real.sqrt 2 * Real.log 2 / 2 =
        Real.log t * (((∑ q ∈ U.primeFactors, Real.log q) - Chebyshev.theta t) /
          Real.sqrt t) +
        (Real.log t * (strict_inventory_second_layer_mass U / Real.sqrt t - Real.sqrt 2) +
          Real.sqrt 2 * Real.log 2 / 2) +
        Real.log t * (strict_inventory_third_layer_mass U / Real.sqrt t) -
        Real.log t * ((Chebyshev.theta (Real.sqrt t) - Real.sqrt t) / Real.sqrt t) -
        Real.log t * ((Chebyshev.psi t - Chebyshev.theta t -
          Chebyshev.theta (Real.sqrt t)) / Real.sqrt t) := by
      rw [hsplit]
      field_simp [ne_of_gt hsqrt]
      ring
    rw [htelescope]
    have h1 := abs_lt.mp hfirst'
    have h2 := abs_lt.mp hsecond'
    have h3 := abs_lt.mp hthird'
    have h4 := abs_lt.mp hsmall.2.1
    have h5 := abs_lt.mp hsmall.2.2
    apply abs_lt.mpr
    constructor <;>
      linarith only [hε, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

#print axioms strict_inventory_root_second_order

end

end D5.S3.Arith.Robin.EulerLayerRootSecondOrder
