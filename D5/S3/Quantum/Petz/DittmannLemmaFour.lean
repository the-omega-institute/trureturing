/- GID: D5/S3/Quantum/Petz/DittmannLemmaFour
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict Dittmann inequalities from positive Stieltjes densities and dominated differentiation. -/

import D5.S3.Quantum.Petz.DensityPositivity
import D5.S3.Quantum.Petz.StieltjesRepresentation
import D5.S3.Quantum.Petz.KernelSmoothness
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace D5.S3.Quantum.Petz.DittmannLemmaFour

open Set Filter MeasureTheory
open scoped Topology
open D5.S3.Quantum.Petz.StieltjesDensity
open D5.S3.Quantum.Petz.StieltjesRepresentation
open D5.S3.Quantum.Petz.DensityPositivity
open D5.S3.Quantum.Petz.KernelSmoothness
open D5.S3.Quantum.Petz.SymmetricKernel
open D5.S3.Quantum.PositiveResolvent.LogMeanResolvents

private lemma rho_measurable (y z : ℝ) : Measurable (rho y z) := by
  unfold rho rP rQ
  split_ifs <;> fun_prop

private lemma resolvent_derivative {r a b : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hr : Measurable r) (ha : Measurable a) (hb : Measurable b)
    (hpos : ∀ t, 0 < t → 0 ≤ r t ∧ 0 ≤ a t ∧ 0 ≤ b t ∧ 0 < x / 2 * a t + b t)
    (hbase : IntegrableOn (fun t => r t / (x / 2 * a t + b t)) (Ioi 0))
    (hcenter : IntegrableOn (fun t => r t / (x * a t + b t)) (Ioi 0)) :
    IntegrableOn (fun t => a t * r t / (x * a t + b t) ^ 2) (Ioi 0) ∧
    HasDerivAt (fun u => ∫ t in Ioi (0 : ℝ), r t / (u * a t + b t))
      (-(∫ t in Ioi (0 : ℝ), a t * r t / (x * a t + b t) ^ 2)) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioi (x / 2)) (F := fun u t => r t / (u * a t + b t))
    (F' := fun u t => -(a t * r t / (u * a t + b t) ^ 2))
    (bound := fun t => (2 / x) * (r t / (x / 2 * a t + b t)))
    (Ioi_mem_nhds (by linarith : x / 2 < x))
    (Eventually.of_forall (fun u => (hr.div ((ha.const_mul u).add hb)).aestronglyMeasurable))
    hcenter ((ha.mul hr).div (((ha.const_mul x).add hb).pow_const 2) |>.neg
      |>.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rcases hpos t ht with ⟨hrp, hap, hbp, hdp⟩
      intro u hu
      change x / 2 < u at hu
      have hdu : x / 2 * a t + b t ≤ u * a t + b t :=
        add_le_add (mul_le_mul_of_nonneg_right hu.le hap) le_rfl
      have hdup : 0 < u * a t + b t := hdp.trans_le hdu
      have hratio : a t / (u * a t + b t) ≤ 2 / x := by
        rw [div_le_div_iff₀ hdup hx]
        nlinarith
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      calc
        a t * r t / (u * a t + b t) ^ 2 =
            (a t / (u * a t + b t)) * (r t / (u * a t + b t)) := by field_simp
        _ ≤ (2 / x) * (r t / (x / 2 * a t + b t)) := by gcongr)
    (hbase.const_mul (2 / x))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rcases hpos t ht with ⟨hrp, hap, hbp, hdp⟩
      intro u hu
      change x / 2 < u at hu
      have hd : 0 < u * a t + b t :=
        hdp.trans_le (add_le_add (mul_le_mul_of_nonneg_right hu.le hap) le_rfl)
      exact ((hasDerivAt_const u (r t)).div
        (((hasDerivAt_id u).mul_const (a t)).add_const (b t)) hd.ne').congr_deriv
        (by dsimp; ring))
  rw [integral_neg] at h
  refine ⟨?_, h.2⟩
  apply h.1.neg.congr
  filter_upwards with t
  exact neg_neg _

private lemma positive_integral {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hn : ∀ t, 0 < t → 0 ≤ f t)
    (hp : ∀ t, 2 < t → t < 3 → 0 < f t) : 0 < ∫ t in Ioi (0 : ℝ), f t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hn t ht) hf).mpr
  have hsub : Ioo (2 : ℝ) 3 ⊆ Function.support f ∩ Ioi 0 := by
    intro t ht
    exact ⟨(hp t ht.1 ht.2).ne', show 0 < t by linarith [ht.1]⟩
  have hv : 0 < volume (Ioo (2 : ℝ) 3) := by norm_num
  exact hv.trans_le (measure_mono hsub)

private lemma first_slot_representation {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) :
    IntegrableOn (fun t => rho y z t / (x + t) ^ 2) (Ioi 0) ∧
    hs1 x y z = ∫ t in Ioi (0 : ℝ), rho y z t / (x + t) ^ 2 := by
  have hd := resolvent_derivative hx (rho_measurable y z) measurable_const measurable_id
    (a := fun _ => 1) (b := id)
    (by intro t ht; exact ⟨(rho_pos hy hz ht).le, by norm_num, ht.le, by positivity⟩)
    (by simpa using rho_integrable (show 0 < x / 2 by positivity) hy hz)
    (by simpa using rho_integrable hx hy hz)
  simp only [mul_one, one_mul, id_eq] at hd
  have he : (fun u => ∫ t in Ioi (0 : ℝ), rho y z t / (u + t)) =ᶠ[𝓝 x]
      (fun u => -hs u y z) := by
    filter_upwards [eventually_gt_nhds hx] with u hu
    exact stieltjes_representation hu hy hz
  have hh := hd.2.congr_of_eventuallyEq he.symm
  have hr := hh.neg.deriv
  have hdouble : (-(fun w => -hs w y z)) = (fun w => hs w y z) := by
    ext w
    exact neg_neg _
  rw [hdouble, neg_neg] at hr
  exact ⟨hd.1, hr⟩

/-- Dittmann (65) holds strictly for two ordered positive evaluation nodes. -/
theorem dittmann65 {x y lam mu : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlam : 0 < lam) (hmu : 0 < mu) (hxy : x < y) :
    0 < hs1 x lam mu - hs1 y lam mu := by
  rcases first_slot_representation hx hlam hmu with ⟨hix, hex⟩
  rcases first_slot_representation hy hlam hmu with ⟨hiy, hey⟩
  rw [hex, hey, ← integral_sub hix hiy]
  apply positive_integral (hix.sub hiy)
  · intro t ht
    have hr := rho_pos hlam hmu ht
    have hd : (x + t) ^ 2 < (y + t) ^ 2 := by nlinarith
    exact (sub_pos.mpr (div_lt_div_of_pos_left hr (by positivity) hd)).le
  · intro t ht hthi
    have htp : 0 < t := by linarith
    have hr := rho_pos hlam hmu htp
    have hd : (x + t) ^ 2 < (y + t) ^ 2 := by nlinarith
    exact sub_pos.mpr (div_lt_div_of_pos_left hr (by positivity) hd)

private lemma repeated_integrable {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t => rho 1 1 t / (v + t * u)) (Ioi 0) := by
  apply ((rho_integrable (div_pos hv hu) zero_lt_one zero_lt_one).const_mul u⁻¹).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  field_simp [hu.ne', (add_pos hv (mul_pos ht hu)).ne',
    (add_pos (div_pos hv hu) ht).ne']
  <;> ring

private lemma repeated_representation {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t in Ioi (0 : ℝ), rho 1 1 t / (v + t * u)) = -hs u u v := by
  have hh := hs_homog hu (div_pos hv hu) zero_lt_one zero_lt_one
  simp only [mul_one, mul_div_cancel₀ _ hu.ne'] at hh
  rw [hs_symm hv hu hu, hs_symm_right hu hv hu] at hh
  calc
    (∫ t in Ioi (0 : ℝ), rho 1 1 t / (v + t * u)) =
        ∫ t in Ioi (0 : ℝ), u⁻¹ * (rho 1 1 t / (v / u + t)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      field_simp [hu.ne', (add_pos hv (mul_pos ht hu)).ne',
        (add_pos (div_pos hv hu) ht).ne']
      <;> ring
    _ = u⁻¹ * (-hs (v / u) 1 1) := by
      rw [integral_const_mul, stieltjes_representation (div_pos hv hu) zero_lt_one zero_lt_one]
    _ = -hs u u v := by rw [hh]; ring

private lemma repeated_first_slot {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t => t * rho 1 1 t / (v + t * u) ^ 2) (Ioi 0) ∧
    2 * hs1 u u v = ∫ t in Ioi (0 : ℝ), t * rho 1 1 t / (v + t * u) ^ 2 := by
  have hd := resolvent_derivative hu (rho_measurable 1 1) measurable_id measurable_const
    (a := id) (b := fun _ => v)
    (by intro t ht; exact ⟨(rho_pos zero_lt_one zero_lt_one ht).le, ht.le, hv.le, by positivity⟩)
    (by simpa [mul_comm, add_comm] using repeated_integrable (show 0 < u / 2 by positivity) hv)
    (by simpa [mul_comm, add_comm] using repeated_integrable hu hv)
  simp only [id_eq] at hd
  have he : (fun w => ∫ t in Ioi (0 : ℝ), rho 1 1 t / (w * t + v)) =ᶠ[𝓝 u]
      (fun w => -hs w w v) := by
    filter_upwards [eventually_gt_nhds hu] with w hw
    simpa [mul_comm, add_comm] using repeated_representation hw hv
  have hh := hd.2.congr_of_eventuallyEq he.symm
  have hr := hh.neg.deriv
  have hdouble : (-(fun w => -hs w w v)) = (fun w => hs w w v) := by
    ext w
    exact neg_neg _
  rw [hdouble, neg_neg, hs_deriv_repeated hu hv] at hr
  exact ⟨by simpa [mul_comm, add_comm] using hd.1, by simpa [mul_comm, add_comm] using hr⟩

/-- Dittmann (63) holds strictly as the repeated node increases. -/
theorem dittmann63 {x y lam : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlam : 0 < lam) (hxy : x < y) : 0 < hs1 x x lam - hs1 y y lam := by
  rcases repeated_first_slot hx hlam with ⟨hix, hex⟩
  rcases repeated_first_slot hy hlam with ⟨hiy, hey⟩
  have hp : 0 < ∫ t in Ioi (0 : ℝ),
      t * rho 1 1 t / (lam + t * x) ^ 2 - t * rho 1 1 t / (lam + t * y) ^ 2 := by
    apply positive_integral (hix.sub hiy)
    · intro t ht
      have hr := mul_pos ht (rho_pos zero_lt_one zero_lt_one ht)
      have hd : (lam + t * x) ^ 2 < (lam + t * y) ^ 2 :=
        (sq_lt_sq₀ (by positivity) (by positivity)).mpr
          (add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hxy ht))
      exact (sub_pos.mpr (div_lt_div_of_pos_left hr (by positivity) hd)).le
    · intro t ht hthi
      have htp : 0 < t := by linarith
      have hr := mul_pos htp (rho_pos zero_lt_one zero_lt_one htp)
      have hd : (lam + t * x) ^ 2 < (lam + t * y) ^ 2 :=
        (sq_lt_sq₀ (by positivity) (by positivity)).mpr
          (add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hxy htp))
      exact sub_pos.mpr (div_lt_div_of_pos_left hr (by positivity) hd)
  rw [integral_sub hix hiy, ← hex, ← hey] at hp
  linarith

private lemma repeated_last_slot {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t => rho 1 1 t / (v + t * u) ^ 2) (Ioi 0) ∧
    hs1 v u u = ∫ t in Ioi (0 : ℝ), rho 1 1 t / (v + t * u) ^ 2 := by
  have hd := resolvent_derivative hv (rho_measurable 1 1) measurable_const
    (measurable_id.mul_const u) (a := fun _ => 1) (b := fun t => t * u)
    (by intro t ht; exact ⟨(rho_pos zero_lt_one zero_lt_one ht).le,
      by norm_num, (mul_pos ht hu).le, by positivity⟩)
    (by simpa using repeated_integrable hu (show 0 < v / 2 by positivity))
    (by simpa using repeated_integrable hu hv)
  simp only [mul_one, one_mul] at hd
  have he : (fun w => ∫ t in Ioi (0 : ℝ), rho 1 1 t / (w + t * u)) =ᶠ[𝓝 v]
      (fun w => -hs w u u) := by
    filter_upwards [eventually_gt_nhds hv] with w hw
    rw [repeated_representation hu hw, hs_symm_right hu hu hw, hs_symm hu hw hu]
  have hh := hd.2.congr_of_eventuallyEq he.symm
  have hr := hh.neg.deriv
  have hdouble : (-(fun w => -hs w u u)) = (fun w => hs w u u) := by
    ext w
    exact neg_neg _
  rw [hdouble, neg_neg] at hr
  exact ⟨hd.1, hr⟩

private lemma hs1_symm_right {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    hs1 x y z = hs1 x z y := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with u hu
  exact hs_symm_right hu hy hz

private lemma exchange_factor {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    t / (y + t * x) ^ 2 - 1 / (y + t * x) ^ 2 -
      t / (x + t * y) ^ 2 + 1 / (x + t * y) ^ 2 =
    (y - x) * (t - 1) ^ 2 * (1 + t) * (x + y) /
      ((y + t * x) ^ 2 * (x + t * y) ^ 2) := by
  field_simp [(add_pos hy (mul_pos ht hx)).ne', (add_pos hx (mul_pos ht hy)).ne']
  <;> ring

/-- Dittmann (62) is strict; its density integrand only vanishes at t = 1. -/
theorem dittmann62 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    0 < 2 * hs1 x x y - hs1 y x x - 2 * hs1 y x y + hs1 x y y := by
  rcases repeated_first_slot hx hy with ⟨hix, hex⟩
  rcases repeated_first_slot hy hx with ⟨hiy, hey⟩
  rcases repeated_last_slot hx hy with ⟨hjx, hfx⟩
  rcases repeated_last_slot hy hx with ⟨hjy, hfy⟩
  rw [hs1_symm_right hy hx hy, hex, hey, hfx, hfy]
  rw [← integral_sub hix hjx]
  change 0 < (∫ t in Ioi (0 : ℝ),
    ((fun t => t * rho 1 1 t / (y + t * x) ^ 2) -
      (fun t => rho 1 1 t / (y + t * x) ^ 2)) t) - _ + _
  rw [← integral_sub (hix.sub hjx) hiy]
  change 0 < (∫ t in Ioi (0 : ℝ),
    (((fun t => t * rho 1 1 t / (y + t * x) ^ 2) -
      (fun t => rho 1 1 t / (y + t * x) ^ 2)) -
      (fun t => t * rho 1 1 t / (x + t * y) ^ 2)) t) + _
  rw [← integral_add ((hix.sub hjx).sub hiy) hjy]
  simp only [Pi.sub_apply]
  have he (t : ℝ) (ht : 0 < t) :
      t * rho 1 1 t / (y + t * x) ^ 2 - rho 1 1 t / (y + t * x) ^ 2 -
        t * rho 1 1 t / (x + t * y) ^ 2 + rho 1 1 t / (x + t * y) ^ 2 =
      rho 1 1 t * ((y - x) * (t - 1) ^ 2 * (1 + t) * (x + y) /
        ((y + t * x) ^ 2 * (x + t * y) ^ 2)) := by
    rw [← exchange_factor hx hy ht]
    ring
  apply positive_integral (((hix.sub hjx).sub hiy).add hjy)
  · intro t ht
    change 0 ≤ t * rho 1 1 t / (y + t * x) ^ 2 - rho 1 1 t / (y + t * x) ^ 2 -
      t * rho 1 1 t / (x + t * y) ^ 2 + rho 1 1 t / (x + t * y) ^ 2
    rw [he t ht]
    exact mul_nonneg (rho_pos zero_lt_one zero_lt_one ht).le (by positivity)
  · intro t ht hthi
    have htp : 0 < t := by linarith
    change 0 < t * rho 1 1 t / (y + t * x) ^ 2 - rho 1 1 t / (y + t * x) ^ 2 -
      t * rho 1 1 t / (x + t * y) ^ 2 + rho 1 1 t / (x + t * y) ^ 2
    rw [he t htp]
    have ht1 : t - 1 ≠ 0 := by linarith
    exact mul_pos (rho_pos zero_lt_one zero_lt_one htp) (by positivity)

/-- Literal (65), retaining both positive auxiliary parameters. -/
theorem claim65 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
    0 ≤ hs1 x lam mu - hs1 y lam mu := by
  intro x y lam mu hx hy hlam hmu hxy
  exact (dittmann65 hx hy hlam hmu hxy).le

/-- Literal (63), retaining the unused positive mu parameter. -/
theorem claim63 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
    0 ≤ hs1 x x lam - hs1 y y lam := by
  intro x y lam mu hx hy hlam hmu hxy
  exact (dittmann63 hx hy hlam hxy).le

/-- Literal (62), retaining both unused positive auxiliary parameters. -/
theorem claim62 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
    0 ≤ 2 * hs1 x x y - hs1 y x x - 2 * hs1 y x y + hs1 x y y := by
  intro x y lam mu hx hy hlam hmu hxy
  exact (dittmann62 hx hy hxy).le

end D5.S3.Quantum.Petz.DittmannLemmaFour
