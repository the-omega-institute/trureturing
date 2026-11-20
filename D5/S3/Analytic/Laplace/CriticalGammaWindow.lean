/- GID: D5/S3/Analytic/Laplace/CriticalGammaWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/CriticalGammaWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit order floor(640a) suppresses the absolute Laplace moment outside the critical multiplicative window. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Real Set
namespace D5.S3.Analytic.Laplace.CriticalGammaWindow

private def moment (k : ℕ) (rate u : ℝ) := u ^ k * exp (-(rate * u)) / k.factorial

private lemma moment_nonneg (k : ℕ) (r : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ moment k r u := by unfold moment; positivity

private lemma moment_integrable (k : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (moment k r) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := r)
    (by linarith [Nat.cast_nonneg (α := ℝ) k] : -1 < (k : ℝ)) (by norm_num) hr
  unfold moment IntegrableOn
  simpa only [rpow_one, Real.rpow_natCast, neg_mul] using hi.div_const (k.factorial : ℝ)

private lemma moment_integral (k : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ u in Ioi 0, moment k r u) = r⁻¹ ^ (k+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ)+1) (by positivity) hr
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial, one_div,
    Real.rpow_add_one (inv_ne_zero hr.ne')] at h
  rw [show moment k r = fun u => (u ^ k * exp (-(r*u))) / (k.factorial : ℝ) from rfl,
    integral_div, h, mul_div_cancel_right₀ _ (by positivity), pow_succ]

private lemma tilt_integral {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)) {S : Set ℝ} (hS : MeasurableSet S)
    (hpos : S ⊆ Ioi 0) (k : ℕ) {r d : ℝ} (hr : 0 < r)
    (htilt : ∀ u ∈ S, (r-510)*u ≤ d) :
    IntegrableOn (fun u => |g u| * moment k 512 u) S ∧
    (∫ u in S, |g u| * moment k 512 u) ≤ M * exp d * r⁻¹ ^ (k+1) := by
  have hm0 : 0 ≤ M := (abs_nonneg (g 0)).trans (by simpa using hM 0 le_rfl)
  have hmajor : IntegrableOn (fun u => M * exp d * moment k r u) (Ioi 0) :=
    (moment_integrable k hr).const_mul (M * exp d)
  have hp u (hu : u ∈ S) : |g u| * moment k 512 u ≤ M * exp d * moment k r u := by
    have hu0 : 0 ≤ u := (show 0 < u from hpos hu).le
    have he : exp (2*u) * exp (-(512*u)) ≤ exp d * exp (-(r*u)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      linarith [htilt u hu]
    calc
      _ ≤ (M * exp (2*u)) * moment k 512 u :=
        mul_le_mul_of_nonneg_right (hM u hu0) (moment_nonneg k _ hu0)
      _ = (M * (u ^ k / k.factorial)) * (exp (2*u) * exp (-(512*u))) := by unfold moment; ring
      _ ≤ (M * (u ^ k / k.factorial)) * (exp d * exp (-(r*u))) := by gcongr
      _ = _ := by unfold moment; ring
  have hmeas : Measurable (fun u => |g u| * moment k 512 u) := by unfold moment; fun_prop
  have hi : IntegrableOn (fun u => |g u| * moment k 512 u) S := by
    refine (hmajor.mono_set hpos).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (moment_nonneg k _ (show 0 < u from hpos hu).le))]
    exact hp u hu
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ u in S, M * exp d * moment k r u :=
      setIntegral_mono_on hi (hmajor.mono_set hpos) hS hp
    _ ≤ ∫ u in Ioi 0, M * exp d * moment k r u := by
      apply setIntegral_mono_set hmajor _ (Filter.Eventually.of_forall hpos)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_nonneg (mul_nonneg hm0 (exp_pos _).le) (moment_nonneg k _ hu.le)
    _ = _ := by rw [integral_const_mul, moment_integral k hr]

private lemma tilt_savings {a : ℝ} (ha : 1 ≤ a) (k : ℕ) (hk : k = ⌊640*a⌋₊) :
    exp (32*a) * (542:ℝ)⁻¹ ^ (k+1) ≤ (1 / 542) * (512:ℝ)⁻¹ ^ k ∧
    exp (-48*a) * (478:ℝ)⁻¹ ^ (k+1) ≤ (1 / 478) * (512:ℝ)⁻¹ ^ k := by
  have hlo : 640*a - 1 ≤ (k:ℝ) := by
    rw [hk]; linarith [Nat.lt_floor_add_one (640*a)]
  have hhi : (k:ℝ) ≤ 640*a := by rw [hk]; exact Nat.floor_le (by linarith)
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<542/512)
  have hr := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<512/478)
  norm_num at hl hr
  have hk0 : 0 ≤ (k:ℝ) := by positivity
  have heL : exp (32*a) ≤ (542/512:ℝ)^k := by
    rw [← Real.exp_log (pow_pos (by norm_num : (0:ℝ)<542/512) k), Real.exp_le_exp, Real.log_pow]
    nlinarith [mul_le_mul_of_nonneg_left hl hk0]
  have heR : exp (-48*a) ≤ (478/512:ℝ)^k := by
    rw [← Real.exp_log (pow_pos (by norm_num : (0:ℝ)<478/512) k), Real.exp_le_exp, Real.log_pow]
    rw [show (478/512:ℝ) = (512/478:ℝ)⁻¹ by norm_num, Real.log_inv]
    nlinarith [mul_le_mul_of_nonneg_left hr hk0]
  constructor
  · apply (mul_le_mul_of_nonneg_right heL (by positivity)).trans_eq
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num [mul_comm]
  · apply (mul_le_mul_of_nonneg_right heR (by positivity)).trans_eq
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num [mul_comm]

/-- The same integer order controls both tails of the absolute moment for every
measurable input with growth bounded by M exp(2u). -/
theorem critical_window_off_mass {a : ℝ} (ha : 1 ≤ a) {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)) :
    let k := ⌊640*a⌋₊
    let f := fun u : ℝ => |g u| * (u ^ k * exp (-(512*u)) / k.factorial)
    let S := Ioi (0:ℝ) \ Icc a (3*a/2)
    a ≤ (k:ℝ) ∧ IntegrableOn f S ∧
      (∫ u in S, f u) ≤ M * (1/542 + 1/478) * (512:ℝ)⁻¹ ^ k := by
  let k := ⌊640*a⌋₊
  let f := fun u : ℝ => |g u| * moment k 512 u
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < 3*a/2 := by linarith
  have hL := tilt_integral hg hM (S := Ioo 0 a) measurableSet_Ioo (fun _ h => h.1)
    k (r := 542) (d := 32*a) (by norm_num) (fun u hu => by linarith [hu.2])
  have hR := tilt_integral hg hM (S := Ioi (3*a/2)) measurableSet_Ioi
    (fun _ hu => hb0.trans hu) k (r := 478) (d := -48*a) (by norm_num)
    (fun u hu => by change 3*a/2 < u at hu; linarith)
  have hsplit : Ioi (0:ℝ) \ Icc a (3*a/2) = Ioo 0 a ∪ Ioi (3*a/2) := by
    ext u; simp only [mem_sdiff, mem_Ioi, mem_Icc, mem_union, mem_Ioo]; grind
  have hdis : Disjoint (Ioo 0 a) (Ioi (3*a/2)) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    change 3*a/2 < u at hv
    linarith [hu.2]
  have hk : a ≤ (k : ℝ) := by
    dsimp [k]; linarith [Nat.lt_floor_add_one (640*a)]
  have hm0 : 0 ≤ M := (abs_nonneg (g 0)).trans (by simpa using hM 0 le_rfl)
  have hsav := tilt_savings ha k rfl
  change a ≤ (k:ℝ) ∧ IntegrableOn f _ ∧ _
  simp only [hsplit]
  refine ⟨hk, hL.1.union hR.1, ?_⟩
  change (∫ u in Ioo 0 a ∪ Ioi (3*a/2), |g u| * moment k 512 u) ≤ _
  rw [setIntegral_union hdis measurableSet_Ioi hL.1 hR.1]
  calc
    _ ≤ _ := add_le_add hL.2 hR.2
    _ ≤ M * ((1/542) * (512:ℝ)⁻¹ ^ k) + M * ((1/478) * (512:ℝ)⁻¹ ^ k) := by
      simpa only [mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left hsav.1 hm0)
        (mul_le_mul_of_nonneg_left hsav.2 hm0)
    _ = _ := by ring

end D5.S3.Analytic.Laplace.CriticalGammaWindow
