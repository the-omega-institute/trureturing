/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime powers contribute exactly two at the square-root tail scale and at most a logarithmic loss in critical negative-part windows. -/

import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Weil.Mertens.WeightedPrimeLimit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Real Filter
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Arith.Robin.EulerLayerRootCorrection (psi_theta_root_limit)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

/-- The tail of the Chebyshev error with weight one per prime. -/
def primeTail (x : ℝ) : ℝ := ∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2

private def diffKernel (t : ℝ) : ℝ := (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2

private def rootKernel (t : ℝ) : ℝ := Real.sqrt t / t ^ 2

private lemma rootKernel_rpow {t : ℝ} (ht : 0 < t) :
    rootKernel t = t ^ (-(3 / 2) : ℝ) := by
  rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub ht,
    Real.rpow_two, ← Real.sqrt_eq_rpow]
  rfl

private lemma root_integrable {x : ℝ} (hx : 0 < x) : IntegrableOn rootKernel (Ioi x) :=
  (integrableOn_Ioi_rpow_of_lt (a := (-(3/2) : ℝ)) (by norm_num) hx).congr_fun
    (fun _ ht => (rootKernel_rpow (hx.trans ht)).symm) measurableSet_Ioi

private lemma root_integral {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi x, rootKernel t = 2 / Real.sqrt x := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun _ ht => rootKernel_rpow (hx.trans ht)),
    integral_Ioi_rpow_of_lt (by norm_num) hx, show (-(3/2) : ℝ) + 1 = -(1/2) by norm_num,
    Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  ring

private lemma diff_integrable : IntegrableOn diffKernel (Ioi 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  apply ((root_integrable one_pos).const_mul C).mono'
    ((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
  change ‖(Chebyshev.psi t - Chebyshev.theta t) / t ^ 2‖ ≤ C * rootKernel t
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))
    (sq_nonneg t))]
  exact (div_le_div_of_nonneg_right (hC t) (sq_nonneg t)).trans_eq (by dsimp [rootKernel]; ring)

private lemma prime_integrable :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioi 1) := by
  apply (chebyshev_error_kernel_integrable.sub diff_integrable).congr_fun _ measurableSet_Ioi
  intro t _
  dsimp [diffKernel]
  ring

private lemma tail_eq {x : ℝ} (hx : 1 ≤ x) :
    Q x - primeTail x = ∫ t in Ioi x, diffKernel t := by
  change (∫ t in Ioi x, (Chebyshev.psi t - t) / t ^ 2) -
    (∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2) = _
  rw [← integral_sub
    (chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi hx))
    (prime_integrable.mono_set (Ioi_subset_Ioi hx))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp [diffKernel, Arith.Robin.CompleteMertensPeak.psiErrorKernel]
  ring

private lemma integral_sandwich {x L H : ℝ} (hx : 1 ≤ x)
    (h : ∀ t, x < t → L * Real.sqrt t ≤ Chebyshev.psi t - Chebyshev.theta t ∧
      Chebyshev.psi t - Chebyshev.theta t ≤ H * Real.sqrt t) :
    L * (2 / Real.sqrt x) ≤ Q x - primeTail x ∧
      Q x - primeTail x ≤ H * (2 / Real.sqrt x) := by
  have hx0 := zero_lt_one.trans_le hx
  have hi := diff_integrable.mono_set (Ioi_subset_Ioi hx)
  have hr := root_integrable hx0
  rw [tail_eq hx, ← root_integral hx0, ← integral_const_mul, ← integral_const_mul]
  constructor
  · apply setIntegral_mono_on (hr.const_mul _) hi measurableSet_Ioi
    intro t ht
    simpa [diffKernel, rootKernel, mul_div_assoc] using
      div_le_div_of_nonneg_right (h t ht).1 (sq_nonneg t)
  · apply setIntegral_mono_on hi (hr.const_mul _) measurableSet_Ioi
    intro t ht
    simpa [diffKernel, rootKernel, mul_div_assoc] using
      div_le_div_of_nonneg_right (h t ht).2 (sq_nonneg t)

private lemma scaled_limit :
    Tendsto (fun x => Real.sqrt x * (Q x - primeTail x)) atTop (𝓝 2) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp psi_theta_root_limit)
    (ε / 4) (by positivity))
  filter_upwards [eventually_ge_atTop (max T 1)] with x hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hs := integral_sandwich (L := 1 - ε / 4) (H := 1 + ε / 4) hx1 (by
    intro t ht
    have hs0 := Real.sqrt_pos.mpr (hx0.trans ht)
    have hp := hT t ((le_max_left _ _).trans (hx.trans ht.le))
    rw [Real.dist_eq, abs_lt] at hp
    exact ⟨((le_div_iff₀ hs0).mp (by linarith)), ((div_le_iff₀ hs0).mp (by linarith))⟩)
  have hs0 := Real.sqrt_pos.mpr hx0
  have hl := mul_le_mul_of_nonneg_left hs.1 hs0.le
  have hu := mul_le_mul_of_nonneg_left hs.2 hs0.le
  rw [Real.dist_eq, abs_lt]
  field_simp [hs0.ne'] at hl hu
  constructor <;> linarith

private lemma pointwise_bound {C : ℝ} (hC : ∀ t, 1 ≤ t →
    Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Q x - primeTail x ∧ Q x - primeTail x ≤ 2 * C / Real.sqrt x := by
  have hs := integral_sandwich (L := 0) (H := C) hx (fun t ht =>
    ⟨by simpa using Chebyshev.theta_le_psi t, hC t (hx.trans ht.le)⟩)
  exact ⟨by simpa only [zero_mul] using hs.1, hs.2.trans_eq (by ring)⟩

private lemma window_bound {C a b : ℝ} (hC : ∀ t, 1 ≤ t →
    Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) (ha : 1 ≤ a) (hab : a ≤ b) :
    let W := ∫ x in a..b, (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x
    0 ≤ W ∧ W ≤ 2 * C * Real.log (b / a) := by
  dsimp only
  have hmem (x : ℝ) (hx : x ∈ uIcc a b) : 1 ≤ x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans hx.1
  have hp : ContinuousOn primeTail (uIcc a b) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi.mono (fun x hx => hmem x hx)
  have hq : ContinuousOn Q (uIcc a b) :=
    chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi.mono (fun x hx => hmem x hx)
  have hi : IntervalIntegrable (fun x => (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x)
      volume a b := (((hp.neg.sup (continuousOn_const (c := (0 : ℝ)))).sub
    (hq.neg.sup (continuousOn_const (c := (0 : ℝ))))).div
    Real.continuous_sqrt.continuousOn (fun x hx => (Real.sqrt_pos.mpr
      (zero_lt_one.trans_le (hmem x hx))).ne')).intervalIntegrable (μ := volume)
  have hxpos (x : ℝ) (hx : x ∈ uIcc a b) := zero_lt_one.trans_le (hmem x hx)
  have hinv : ContinuousOn (fun x : ℝ => 2 * C * x⁻¹) (uIcc a b) :=
    continuousOn_const.mul (continuousOn_id.inv₀ fun x hx => (hxpos x hx).ne')
  have horder (x : ℝ) (hx : x ∈ Icc a b) :
      0 ≤ (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x ∧
      (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x ≤ 2 * C * x⁻¹ := by
    have hx1 := ha.trans hx.1
    have h := pointwise_bound hC hx1
    have ht : primeTail x ≤ Q x := by linarith [h.1]
    have hgap : max (-primeTail x) 0 - max (-Q x) 0 ≤ Q x - primeTail x := by
      rcases le_total (Q x) 0 with hq0 | hq0 <;> rcases le_total (primeTail x) 0 with hp0 | hp0
        <;> simp [max_def] <;> split_ifs <;> linarith
    have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx1)
    refine ⟨div_nonneg (sub_nonneg.mpr (max_le_max (neg_le_neg ht) le_rfl)) hs0.le,
      (div_le_div_of_nonneg_right (hgap.trans h.2) hs0.le).trans_eq ?_⟩
    rw [div_div, ← sq, Real.sq_sqrt (zero_le_one.trans hx1), div_eq_mul_inv]
  refine ⟨intervalIntegral.integral_nonneg hab (fun x hx => (horder x hx).1), ?_⟩
  calc
    _ ≤ ∫ x in a..b, 2 * C * x⁻¹ := intervalIntegral.integral_mono_on hab hi
      hinv.intervalIntegrable (fun x hx => (horder x hx).2)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv (fun h => (hxpos 0 h).false)]

/-- The exact root-scale correction and the cost of suppressing prime powers in
critical negative-part windows, for every Chebyshev majorant on the same domain. -/
theorem prime_power_window_correction :
    Tendsto (fun x => Real.sqrt x * (Q x - primeTail x)) atTop (𝓝 2) ∧
    ∀ C : ℝ, (∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) →
      (∀ x, 1 ≤ x → 0 ≤ Q x - primeTail x ∧ Q x - primeTail x ≤ 2 * C / Real.sqrt x) ∧
      ∀ a b : ℝ, 1 ≤ a → a ≤ b →
        let W := ∫ x in a..b, (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x
        0 ≤ W ∧ W ≤ 2 * C * Real.log (b / a) :=
  ⟨scaled_limit, fun _ hC => ⟨fun _ => pointwise_bound hC, fun _ _ => window_bound hC⟩⟩

private lemma prime_kernel_interval {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) volume u v :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).2
    (prime_integrable.mono_set fun _ ht => hu.trans_lt ht.1)

private lemma frozen_count_kernel_integral (c : ℝ) {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) :
    ∫ t in u..v, (t - c) / t ^ 2 =
      Real.log (v / u) + c * (v⁻¹ - u⁻¹) := by
  have htpos (t : ℝ) (ht : t ∈ uIcc u v) : 0 < t :=
    hu.trans_le ((uIcc_of_le huv ▸ ht).1)
  have hi : IntervalIntegrable (fun t : ℝ => (t - c) / t ^ 2) volume u v :=
    ((continuous_id.sub continuous_const).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun t ht => (pow_pos (htpos t ht) 2).ne')).intervalIntegrable
  calc
    _ = (Real.log v + c * v⁻¹) - (Real.log u + c * u⁻¹) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
      intro t ht
      have ht0 := (htpos t ht).ne'
      convert (Real.hasDerivAt_log ht0).add ((hasDerivAt_inv ht0).const_mul c) using 1
      field_simp
      ring
    _ = _ := by rw [Real.log_div (hu.trans_le huv).ne' hu.ne']; ring

private lemma primeTail_reciprocal_tangent {x z : ℝ} (hx : 1 ≤ x) (hz : 1 ≤ z) :
    primeTail z - primeTail x ≤
      Real.log (z / x) + Chebyshev.theta x * (z⁻¹ - x⁻¹) := by
  have hx0 := zero_lt_one.trans_le hx
  have hz0 := zero_lt_one.trans_le hz
  obtain h | h := le_total x z
  · have hi := (prime_kernel_interval hx h).neg
    have hc : IntervalIntegrable (fun t : ℝ => (t - Chebyshev.theta x) / t ^ 2) volume x z :=
      ((continuous_id.sub continuous_const).continuousOn.div
        (continuous_id.pow 2).continuousOn
        (fun t ht => (pow_pos (hx0.trans_le ((uIcc_of_le h ▸ ht).1)) 2).ne')).intervalIntegrable
    calc
      primeTail z - primeTail x = ∫ t in x..z, -((Chebyshev.theta t - t) / t ^ 2) := by
        rw [intervalIntegral.integral_neg]
        rw [← intervalIntegral.integral_Ioi_sub_Ioi
          (prime_integrable.mono_set (Ioi_subset_Ioi hx)) h, neg_sub]
        rfl
      _ ≤ ∫ t in x..z, (t - Chebyshev.theta x) / t ^ 2 := by
        apply intervalIntegral.integral_mono_on h hi hc
        intro t ht
        change -((Chebyshev.theta t - t) / t ^ 2) ≤ _
        rw [← neg_div]
        exact div_le_div_of_nonneg_right (by linarith [Chebyshev.theta_mono ht.1]) (sq_nonneg t)
      _ = _ := frozen_count_kernel_integral _ hx0 h
  · have hi := prime_kernel_interval hz h
    have hc : IntervalIntegrable (fun t : ℝ => (t - Chebyshev.theta x) / t ^ 2) volume z x :=
      ((continuous_id.sub continuous_const).continuousOn.div
        (continuous_id.pow 2).continuousOn
        (fun t ht => (pow_pos (hz0.trans_le ((uIcc_of_le h ▸ ht).1)) 2).ne')).intervalIntegrable
    have hle := intervalIntegral.integral_mono_on h hc hi.neg (fun t ht => by
      change _ ≤ -((Chebyshev.theta t - t) / t ^ 2)
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (by linarith [Chebyshev.theta_mono ht.2]) (sq_nonneg t))
    change (∫ t in z..x, (t - Chebyshev.theta x) / t ^ 2) ≤
      ∫ t in z..x, -((Chebyshev.theta t - t) / t ^ 2) at hle
    rw [intervalIntegral.integral_neg, frozen_count_kernel_integral _ hz0 h] at hle
    have htail : primeTail z - primeTail x = ∫ t in z..x, (Chebyshev.theta t - t) / t ^ 2 :=
      intervalIntegral.integral_Ioi_sub_Ioi (prime_integrable.mono_set (Ioi_subset_Ioi hz)) h
    rw [Real.log_div hx0.ne' hz0.ne'] at hle
    rw [Real.log_div hz0.ne' hx0.ne', htail]
    linarith

private lemma primeTail_persists {x z r : ℝ} (hx : 1 ≤ x) (hz : 1 ≤ z)
    (hr : 0 < r) (hr' : r ≤ 1 / 2) (hlo : (1 - r) * x ≤ z) (hhi : z ≤ (1 + r) * x)
    (hside : (Chebyshev.theta x - x) * (z⁻¹ - x⁻¹) ≤ 0) :
    primeTail z ≤ primeTail x + 2 * r ^ 2 := by
  have hx0 := zero_lt_one.trans_le hx
  have hz0 := zero_lt_one.trans_le hz
  have habs : |z - x| ≤ r * x := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsquare : (z - x) ^ 2 ≤ (r * x) ^ 2 := sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
  have hhalf : x / 2 ≤ z := by nlinarith
  have hquad : (z - x) ^ 2 / (z * x) ≤ 2 * r ^ 2 := by
    apply (div_le_iff₀ (mul_pos hz0 hx0)).2
    exact hsquare.trans (by
      have h := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ 2 * r ^ 2 * x by positivity)
      linarith only [h, show (r * x) ^ 2 = x / 2 * (2 * r ^ 2 * x) by ring,
        show 2 * r ^ 2 * (z * x) = z * (2 * r ^ 2 * x) by ring])
  have hlog := Real.log_le_sub_one_of_pos (div_pos hz0 hx0)
  have htan := primeTail_reciprocal_tangent hx hz
  have hid : z / x - 1 + x * (z⁻¹ - x⁻¹) = (z - x) ^ 2 / (z * x) := by
    field_simp
    ring
  linarith

/-- A negative value of the prime-only tail forces mass in any window with room on both sides. -/
theorem prime_tail_negative_window_lower {a b x r : ℝ}
    (ha : 1 ≤ a) (hlo : a ≤ (1 - r) * x) (hhi : (1 + r) * x ≤ b)
    (hr : 0 < r) (hr' : r ≤ 1 / 2) (hdepth : primeTail x ≤ -4 * r ^ 2) :
    r ^ 3 * Real.sqrt x ≤ ∫ z in a..b, max (-primeTail z) 0 / Real.sqrt z := by
  have hx0 : 0 < x := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - r by linarith) h
    linarith
  have hleft : (1 - r) * x ≤ x := by nlinarith
  have hright : x ≤ (1 + r) * x := by nlinarith
  have hx : 1 ≤ x := ha.trans (hlo.trans hleft)
  have hab := hlo.trans (hleft.trans (hright.trans hhi))
  let f : ℝ → ℝ := fun z => max (-primeTail z) 0 / Real.sqrt z
  have hcont : ContinuousOn f (uIcc a b) := by
    apply ((prime_integrable.continuousOn_Ici_primitive_Ioi.mono
      (fun z hz => ha.trans ((uIcc_of_le hab ▸ hz).1))).neg.sup continuousOn_const).div
      Real.continuous_sqrt.continuousOn
    intro z hz
    exact (Real.sqrt_pos.mpr (zero_lt_one.trans_le (ha.trans ((uIcc_of_le hab ▸ hz).1)))).ne'
  have hf : IntervalIntegrable f volume a b := hcont.intervalIntegrable
  have hnonneg : ∀ z, 0 ≤ f z := fun _ =>
    div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have hlower {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
      (hwidth : v - u = r * x)
      (hpersist : ∀ z ∈ Icc u v, z ≤ (1 + r) * x ∧ primeTail z ≤ -2 * r ^ 2) :
      r ^ 3 * Real.sqrt x ≤ ∫ z in a..b, f z := by
    have hsub : uIcc u v ⊆ uIcc a b := by
      rw [uIcc_of_le huv, uIcc_of_le hab]
      exact Icc_subset_Icc hau hvb
    have hsq := Real.sq_sqrt hx0.le
    have hs := Real.sqrt_pos.mpr hx0
    calc
      r ^ 3 * Real.sqrt x = (v - u) * (r ^ 2 / Real.sqrt x) := by
        rw [hwidth]
        field_simp
        exact hsq
      _ = ∫ _ in u..v, r ^ 2 / Real.sqrt x := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ z in u..v, f z := by
        apply intervalIntegral.integral_mono_on huv intervalIntegrable_const
          (hcont.mono hsub).intervalIntegrable
        intro z hz
        obtain ⟨hzhi, hzd⟩ := hpersist z hz
        have hz0 := zero_lt_one.trans_le (ha.trans (hau.trans hz.1))
        have hzs : Real.sqrt z ≤ 2 * Real.sqrt x := by
          rw [← Real.sqrt_sq (show 0 ≤ 2 * Real.sqrt x by positivity)]
          apply Real.sqrt_le_sqrt
          nlinarith
        calc
          r ^ 2 / Real.sqrt x = (2 * r ^ 2) / (2 * Real.sqrt x) := by ring
          _ ≤ (2 * r ^ 2) / Real.sqrt z :=
            div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hz0) hzs
          _ ≤ f z := div_le_div_of_nonneg_right (by linarith [le_max_left (-primeTail z) 0])
            (Real.sqrt_nonneg z)
      _ ≤ ∫ z in a..b, f z := intervalIntegral.integral_mono_interval hau huv hvb
        (Eventually.of_forall hnonneg) hf
  rcases le_total (Chebyshev.theta x) x with h | h
  · apply hlower hlo hleft (hright.trans hhi) (by ring)
    intro z hz
    refine ⟨hz.2.trans hright, ?_⟩
    have hz1 := ha.trans (hlo.trans hz.1)
    have hsign := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h)
      (sub_nonneg.mpr (inv_anti₀ (zero_lt_one.trans_le hz1) hz.2))
    linarith [primeTail_persists hx hz1 hr hr' hz.1 (hz.2.trans hright) hsign]
  · apply hlower (hlo.trans hleft) hright hhi (by ring)
    intro z hz
    refine ⟨hz.2, ?_⟩
    have hz1 := hx.trans hz.1
    have hsign := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h)
      (sub_nonpos.mpr (inv_anti₀ hx0 hz.1))
    linarith [primeTail_persists hx hz1 hr hr' (hleft.trans hz.1) hz.2 hsign]

/-- A sequence with consecutive ratios tending to one intersects every
sufficiently late interval of a fixed relative width. -/
private theorem eventual_sequence_hits_relative_window {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    (hratio : Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 1)) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (N : ℕ) :
    ∀ᶠ y : ℝ in atTop, ∃ n ≥ N, a * y ≤ u n ∧ u n ≤ b * y := by
  have hb := ha.trans hab
  have hmargin : 1 < b / a := (lt_div_iff₀ ha).2 (by simpa using hab)
  have hsteps : ∀ᶠ n in atTop, 0 < u n ∧ u (n + 1) / u n ≤ b / a :=
    (hu.eventually_gt_atTop 0).and
      ((hratio.eventually (gt_mem_nhds hmargin)).mono fun _ h => h.le)
  obtain ⟨T, hT⟩ := eventually_atTop.1 hsteps
  let S := max T N
  have hlarge : ∀ᶠ y : ℝ in atTop, u S / a < y := eventually_gt_atTop _
  filter_upwards [hlarge] with y hy
  have hbelow : u S < a * y := by
    simpa [mul_comm] using (div_lt_iff₀ ha).1 hy
  have hex : ∃ n, a * y ≤ u (S + n) := by
    obtain ⟨K', hK'⟩ := eventually_atTop.1 (hu.eventually_ge_atTop (a * y))
    exact ⟨K', hK' _ (Nat.le_add_left _ _)⟩
  have hhit := Nat.find_spec hex
  have hindex : Nat.find hex ≠ 0 := by
    intro hzero
    rw [hzero, Nat.add_zero] at hhit
    exact (not_le_of_gt hbelow) hhit
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero hindex
  have hbefore : u (S + n) < a * y :=
    not_le.mp (Nat.find_min hex (by omega : n < Nat.find hex))
  obtain ⟨hpos, hstep⟩ := hT (S + n)
    ((le_max_left T N).trans (Nat.le_add_right S n))
  have hupper : u ((S + n) + 1) ≤ b / a * u (S + n) := (div_le_iff₀ hpos).1 hstep
  have hproduct : b / a * (a * y) = b * y := by
    field_simp
  refine ⟨S + (n + 1), (le_max_right T N).trans (Nat.le_add_right S _), ?_, ?_⟩
  · simpa [hn] using hhit
  · rw [← Nat.add_assoc, ← hproduct]
    exact hupper.trans (mul_le_mul_of_nonneg_left hbefore.le (div_nonneg hb.le ha.le))


open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity (complete_chebyshev_tail_identity)

/-- The log-window integral of the actual complete remainder is dominated by
the weighted negative mass of the prime-only tail. -/
private theorem integral_U_exp_le_prime_window {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ u in Real.log a..Real.log b, U (Real.exp u)) ≤
      Real.sqrt b * (∫ z in a..b, max (-primeTail z) 0 / Real.sqrt z) := by
  have ha0 : 0 < a := by linarith
  have hb0 := ha0.trans_le hab
  have hla := Real.log_le_log ha0 hab
  have hmem {z : ℝ} (hz : z ∈ uIcc a b) : 1 ≤ z := by
    have hz' := uIcc_of_le hab ▸ hz
    linarith [hz'.1]
  have qContinuous : ContinuousOn Q (Ici 1) :=
    chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi
  have hpri : ContinuousOn primeTail (uIcc a b) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi.mono (fun z hz => hmem hz)
  have hmass : IntervalIntegrable (fun z => max (-primeTail z) 0 / Real.sqrt z) volume a b :=
    ((hpri.neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun z hz => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hmem hz))).ne')).intervalIntegrable
  have htwo {u : ℝ} (hu : u ∈ uIcc (Real.log a) (Real.log b)) : 2 ≤ Real.exp u := by
    rw [uIcc_of_le hla] at hu
    exact ha.trans (by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hu.1)
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have htailOrder (z : ℝ) (hz : 1 ≤ z) : primeTail z ≤ Q z := by
    have hh := ((prime_power_window_correction.2 C (fun z _ => hC z)).1 z hz).1
    linarith
  calc
    _ = ∫ u in Real.log a..Real.log b, (-Q (Real.exp u)) * Real.exp u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hQ := complete_chebyshev_tail_identity chebyshev_error_kernel_integrable (htwo hu)
      change Q (Real.exp u) = _ at hQ
      change U (Real.exp u) = -Q (Real.exp u) * Real.exp u
      rw [hQ, U]
      field_simp [(Real.exp_pos u).ne']
      ring
    _ = ∫ z in a..b, -Q z := by
      have hchange := intervalIntegral.integral_comp_mul_deriv'
        (a := Real.log a) (b := Real.log b) (f := Real.exp) (f' := Real.exp)
        (g := fun z => -Q z) (fun u _ => Real.hasDerivAt_exp u)
        Real.continuous_exp.continuousOn (qContinuous.neg.mono (by
          rintro _ ⟨u, hu, rfl⟩
          exact (by norm_num : (1 : ℝ) ≤ 2).trans (htwo hu)))
      simpa [Function.comp_def, Real.exp_log ha0, Real.exp_log hb0] using hchange
    _ ≤ ∫ z in a..b, Real.sqrt b * (max (-primeTail z) 0 / Real.sqrt z) := by
      refine intervalIntegral.integral_mono_on hab (qContinuous.neg.mono (fun z hz => hmem hz)).intervalIntegrable
        (hmass.const_mul _) (fun z hz => ?_)
      have hz1 := hmem (uIcc_of_le hab ▸ hz)
      have hz0 := zero_lt_one.trans_le hz1
      have hweight := Real.sqrt_le_sqrt hz.2
      calc
        -Q z ≤ max (-primeTail z) 0 :=
          (neg_le_neg (htailOrder z hz1)).trans (le_max_left _ _)
        _ = Real.sqrt z * (max (-primeTail z) 0 / Real.sqrt z) := by
          field_simp [(Real.sqrt_pos.mpr hz0).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_right hweight
          (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
    _ = _ := intervalIntegral.integral_const_mul _ _


/-- Logarithmically frequent positive remainders force a lower bound in each late window. -/
private theorem eventual_prime_window_of_log_frequency {u : ℕ → ℝ} {β c M k θ : ℝ}
    (hu : Tendsto u atTop atTop)
    (hratio : Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 1))
    (hc : 0 < c) (hk : 1 < k) (hk' : k < 3 / 2)
    (hθ : 0 < θ) (hβ : θ + 1 / 2 < β)
    (hpeaks : ∀ᶠ n in atTop,
      c * Real.exp (β * u n) / (u n) ^ M ≤
        ∫ t in u n - Real.log 2..u n, U (Real.exp t)) :
    ∀ᶠ y : ℝ in atTop, Real.exp (θ * k * y) ≤
      ∫ z in Real.exp y..Real.exp ((3 / 2) * y), max (-primeTail z) 0 / Real.sqrt z := by
  let mass : ℝ → ℝ := fun z => max (-primeTail z) 0 / Real.sqrt z
  let δ : ℝ := β - (θ + 1 / 2)
  have hδ : 0 < δ := sub_pos.mpr hβ
  have hexp : Tendsto (fun n => Real.exp (δ * u n) / (u n) ^ M) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop M δ hδ).comp hu
  have habsorb := hexp.eventually_ge_atTop c⁻¹
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpeaks.and habsorb)
  have hhit := eventual_sequence_hits_relative_window hu hratio
    (show 0 < k from zero_lt_one.trans hk) hk' N
  have hlim : ∀ᶠ y : ℝ in atTop, max (Real.log 2) (Real.log 2 / (k - 1)) ≤ y :=
    eventually_ge_atTop _
  filter_upwards [hhit, hlim] with y hy hy'
  obtain ⟨n, hn, hnlo, hnhi⟩ := hy
  obtain ⟨hpeak, habs⟩ := hN n hn
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hgap : y + Real.log 2 ≤ u n := by
    have h := (div_le_iff₀ (sub_pos.mpr hk)).1 ((le_max_right _ _).trans hy')
    linarith
  have hA : Real.exp y ≤ Real.exp (u n - Real.log 2) := Real.exp_le_exp.mpr (by linarith)
  have hA2 : 2 ≤ Real.exp y := by
    have h := Real.exp_le_exp.mpr ((le_max_left _ _).trans hy')
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hAorder : Real.exp (u n - Real.log 2) ≤ Real.exp (u n) :=
    Real.exp_le_exp.mpr (by linarith)
  have hB : Real.exp (u n) ≤ Real.exp ((3 / 2) * y) := Real.exp_le_exp.mpr hnhi
  have hcover := le_trans hA (hAorder.trans hB)
  have hmass : IntervalIntegrable mass volume (Real.exp y) (Real.exp ((3 / 2) * y)) := by
    have hcont : ContinuousOn primeTail (uIcc (Real.exp y) (Real.exp ((3 / 2) * y))) :=
      prime_integrable.continuousOn_Ici_primitive_Ioi.mono (fun _ ht =>
        (by norm_num : (1 : ℝ) ≤ 2).trans (hA2.trans ((uIcc_of_le hcover ▸ ht).1)))
    apply ((hcont.neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn _).intervalIntegrable
    intro z hz
    exact (Real.sqrt_pos.mpr ((Real.exp_pos y).trans_le ((uIcc_of_le hcover ▸ hz).1))).ne'
  have hmassSub := intervalIntegral.integral_mono_interval hA hAorder hB
    (Eventually.of_forall (fun z => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg z))) hmass
  have hcomp := integral_U_exp_le_prime_window (hA2.trans hA) hAorder
  simp only [Real.log_exp] at hcomp
  have hcoefficient : 1 ≤ c * (Real.exp (δ * u n) / (u n) ^ M) := by
    have hp := mul_le_mul_of_nonneg_left habs hc.le
    simpa [mul_inv_cancel₀ hc.ne'] using hp
  have hexp_eq : Real.exp ((θ + 1 / 2) * u n) *
      (c * (Real.exp (δ * u n) / (u n) ^ M)) = c * Real.exp (β * u n) / (u n) ^ M := by
    rw [show Real.exp ((θ + 1 / 2) * u n) *
          (c * (Real.exp (δ * u n) / (u n) ^ M)) =
        c * (Real.exp ((θ + 1 / 2) * u n) * Real.exp (δ * u n)) / (u n) ^ M by ring,
      ← Real.exp_add]
    congr 3
    dsimp [δ]
    ring
  have hPeak : Real.exp ((θ + 1 / 2) * u n) ≤
      Real.sqrt (Real.exp (u n)) *
        (∫ z in Real.exp (u n - Real.log 2)..Real.exp (u n), mass z) := by
    have hc' := mul_le_mul_of_nonneg_left hcoefficient (Real.exp_nonneg ((θ + 1 / 2) * u n))
    rw [mul_one, hexp_eq] at hc'
    exact hc'.trans (hpeak.trans hcomp)
  have hhalf : Real.sqrt (Real.exp (u n)) = Real.exp (u n / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [hhalf, show (θ + 1 / 2) * u n = u n / 2 + θ * u n by ring, Real.exp_add] at hPeak
  have hnWindow := le_of_mul_le_mul_left hPeak (Real.exp_pos (u n / 2))
  exact (Real.exp_le_exp.mpr (by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnlo hθ.le)).trans
    (hnWindow.trans hmassSub)


/-- A logarithmically frequent positive excursion of the complete remainder
forces weighted negative prime-tail mass in every sufficiently late power window. -/
theorem eventual_prime_window_lower_of_log_frequency {u : ℕ → ℝ} {β c M : ℝ}
    (hu : Tendsto u atTop atTop)
    (hratio : Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 1))
    (hc : 0 < c) (hβ : 1 / 2 < β)
    (hpeaks : ∀ᶠ n in atTop,
      c * Real.exp (β * u n) / (u n) ^ M ≤
        ∫ t in u n - Real.log 2..u n, U (Real.exp t))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, Real.exp (((3 / 2) * (β - 1 / 2) - ε) * y) ≤
      ∫ z in Real.exp y..Real.exp ((3 / 2) * y), max (-primeTail z) 0 / Real.sqrt z := by
  have hden : 0 < β + 1 := by linarith
  have hmin : 0 < min (1 / 2) (min (β - 1 / 2) (ε / (β + 1))) :=
    lt_min (by norm_num) (lt_min (sub_pos.mpr hβ) (div_pos hε hden))
  obtain ⟨d, hd, hd'⟩ := exists_between hmin
  have hd0 : d < 1 / 2 := lt_of_lt_of_le hd' (min_le_left _ _)
  have hd1 : d < β - 1 / 2 := hd'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : d * (β + 1) < ε := (lt_div_iff₀ hden).1
    (hd'.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hh := eventual_prime_window_of_log_frequency
    (u := u) (k := 3 / 2 - d) (θ := β - 1 / 2 - d)
    hu hratio hc (by linarith) (by linarith) (by linarith) (by linarith) hpeaks
  filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with y hy hy0
  apply le_trans _ hy
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ hy0
  nlinarith only [hd2, sq_nonneg d]


end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
