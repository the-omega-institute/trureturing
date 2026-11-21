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

private lemma variable_tilt {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)) {S : Set ℝ} (hS : MeasurableSet S)
    (hpos : S ⊆ Ioi 0) (k : ℕ) {σ r d : ℝ} (hr : 0 < r)
    (htilt : ∀ u ∈ S, (r-σ+2)*u ≤ d) :
    IntegrableOn (fun u => |g u| * moment k σ u) S ∧
    (∫ u in S, |g u| * moment k σ u) ≤ M * exp d * r⁻¹ ^ (k+1) := by
  have hm0 : 0 ≤ M := (abs_nonneg (g 0)).trans (by simpa using hM 0 le_rfl)
  have hmajor : IntegrableOn (fun u => M * exp d * moment k r u) (Ioi 0) :=
    (moment_integrable k hr).const_mul (M * exp d)
  have hp u (hu : u ∈ S) : |g u| * moment k σ u ≤ M * exp d * moment k r u := by
    have hu0 : 0 ≤ u := (show 0 < u from hpos hu).le
    have he : exp (2*u) * exp (-(σ*u)) ≤ exp d * exp (-(r*u)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      linarith [htilt u hu]
    calc
      _ ≤ (M * exp (2*u)) * moment k σ u :=
        mul_le_mul_of_nonneg_right (hM u hu0) (moment_nonneg k _ hu0)
      _ = (M * (u ^ k / k.factorial)) * (exp (2*u) * exp (-(σ*u))) := by unfold moment; ring
      _ ≤ (M * (u ^ k / k.factorial)) * (exp d * exp (-(r*u))) := by gcongr
      _ = _ := by unfold moment; ring
  have hmeas : Measurable (fun u => |g u| * moment k σ u) := by unfold moment; fun_prop
  have hi : IntegrableOn (fun u => |g u| * moment k σ u) S := by
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

private lemma tilt_integral {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)) {S : Set ℝ} (hS : MeasurableSet S)
    (hpos : S ⊆ Ioi 0) (k : ℕ) {r d : ℝ} (hr : 0 < r)
    (htilt : ∀ u ∈ S, (r-510)*u ≤ d) :
    IntegrableOn (fun u => |g u| * moment k 512 u) S ∧
    (∫ u in S, |g u| * moment k 512 u) ≤ M * exp d * r⁻¹ ^ (k+1) := by
  apply variable_tilt hg hM hS hpos k hr
  intro u hu
  convert htilt u hu using 1; ring

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

private lemma decay_rates {h b : ℝ} (hh : 1 < h) (hb : h < b) (T : ℝ) :
    ∀ᶠ σ : ℝ in Filter.atTop, 2 < σ * (1-h/b) ∧
      T < σ * (h * log h - h + 1) - 2 ∧
      T < σ * (b-h-h * log (b/h)) - 2*b := by
  have hh0 : 0 < h := by linarith
  have hb0 := hh0.trans hb
  have hratio : 1 < b / h := (one_lt_div hh0).2 hb
  have hL := Real.log_lt_sub_one_of_pos (inv_pos.2 hh0) (ne_of_lt <| inv_lt_one_of_one_lt₀ hh)
  rw [Real.log_inv] at hL
  have hLpos : 0 < h * log h - h + 1 := by
    have := mul_lt_mul_of_pos_left hL hh0
    rw [mul_sub, mul_inv_cancel₀ hh0.ne', mul_one] at this
    linarith
  have hR := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos (by positivity : 0 < b/h) hratio.ne') hh0
  have hRpos : 0 < b - h - h * log (b/h) := by
    rw [mul_sub, (show h * (b / h) = b by field_simp), mul_one] at hR
    linarith
  have hsign : 0 < 1 - h/b := sub_pos.2 ((div_lt_one hb0).2 hb)
  filter_upwards [(Filter.tendsto_id.atTop_mul_const hsign).eventually_gt_atTop 2,
    (Filter.tendsto_id.atTop_mul_const hLpos).eventually_gt_atTop (T+2),
    (Filter.tendsto_id.atTop_mul_const hRpos).eventually_gt_atTop (T+2*b)] with σ hs hL hR
  exact ⟨hs, by change T+2 < σ * _ at hL; linarith, by change T+2*b < σ * _ at hR; linarith⟩

private lemma floor_savings {h b σ a : ℝ} (hh : 1 < h) (hb : h < b)
    (hσ : 0 < σ) (ha : 0 < a) :
    let k := ⌊σ*h*a⌋₊
    exp ((σ*h-σ+2)*a) * (σ*h)⁻¹ ^ (k+1) ≤
      σ⁻¹ ^ k * (exp (-(σ*(h*log h-h+1)-2)*a) / σ) ∧
    exp ((σ*(h/b)-σ+2)*(b*a)) * (σ*(h/b))⁻¹ ^ (k+1) ≤
      σ⁻¹ ^ k * (b/(h*σ)*exp (-(σ*(b-h-h*log (b/h))-2*b)*a)) := by
  let k := ⌊σ*h*a⌋₊
  change _ ≤ σ⁻¹ ^ k * _ ∧ _ ≤ σ⁻¹ ^ k * _
  have hh0 : 0 < h := by linarith
  have hb0 := hh0.trans hb
  have hfloorL : σ*h*a < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hfloorR : (k:ℝ) ≤ σ*h*a := Nat.floor_le (by positivity)
  have hlogL := Real.log_pos hh
  have hlogR := Real.log_pos ((one_lt_div hh0).2 hb)
  constructor
  · let d := (σ*h-σ+2)*a
    calc
      _ = σ⁻¹ ^ k * (exp (d - ((k:ℝ)+1) * log h) / σ) := by
        rw [Real.exp_sub, show (k:ℝ)+1 = ((k+1:ℕ):ℝ) by norm_cast,
          Real.exp_nat_mul, Real.exp_log hh0, mul_inv, mul_pow, pow_succ σ⁻¹]
        simp only [div_eq_mul_inv, inv_pow]; ring
      _ ≤ _ := by
        gcongr
        dsimp [d]
        nlinarith [mul_lt_mul_of_pos_right hfloorL hlogL]
  · let q := b/h
    let d := (σ*(h/b)-σ+2)*(b*a)
    have hq : 0 < q := div_pos hb0 hh0
    calc
      _ = σ⁻¹ ^ k * (q/σ * exp (d + (k:ℝ) * log q)) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hq, mul_inv, mul_pow,
          show (h/b)⁻¹ = q by simp [q], pow_succ σ⁻¹, pow_succ q]
        simp only [div_eq_mul_inv]; dsimp [d,k]; ring
      _ ≤ _ := by
        rw [show q/σ = b/(h*σ) by dsimp [q]; ring]
        gcongr
        dsimp [d,q]
        have heq : σ*(h/b)*(b*a) = σ*h*a := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right hfloorR hlogR.le]

/-- The two optimized exponential tilts for a variable window. The same chosen integer order gives
both bounds down to arbitrarily small positive cutoffs, where the floor can be zero. -/
private lemma mass_at_rate {h b σ : ℝ} (hh : 1 < h) (hb : h < b) (hσ : 0 < σ)
    (hsign : 2 < σ * (1-h/b)) {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)) :
    let k := ⌊σ*h*a⌋₊
    let f := fun u : ℝ => |g u| * (u ^ k * exp (-(σ*u)) / k.factorial)
    let S := Ioi (0:ℝ) \ Icc a (b*a)
    IntegrableOn f S ∧ (∫ u in S, f u) ≤ M * σ⁻¹ ^ k *
      (exp (-(σ*(h*log h-h+1)-2)*a) / σ +
         b/(h*σ)*exp (-(σ*(b-h-h*log (b/h))-2*b)*a)) := by
  let k := ⌊σ*h*a⌋₊
  let f := fun u : ℝ => |g u| * moment k σ u
  have hh0 : 0 < h := by linarith
  have hb1 := hh.trans hb
  have hba : a < b*a := by nlinarith [mul_pos (sub_pos.2 hb1) ha]
  have hLrate : 0 ≤ σ*h-σ+2 := by nlinarith [mul_pos hσ (sub_pos.2 hh)]
  have hRrate : σ*(h/b)-σ+2 ≤ 0 := by linarith
  have hL := variable_tilt hg hM (S := Ioo 0 a) measurableSet_Ioo (fun _ hu => hu.1)
    k (σ := σ) (r := σ*h) (d := (σ*h-σ+2)*a) (by positivity) (fun _ hu =>
      mul_le_mul_of_nonneg_left hu.2.le hLrate)
  have hR := variable_tilt hg hM (S := Ioi (b*a)) measurableSet_Ioi
    (fun _ hu => (ha.trans hba).trans hu) k (σ := σ) (r := σ*(h/b))
    (d := (σ*(h/b)-σ+2)*(b*a)) (by exact mul_pos hσ (div_pos hh0 (hh0.trans hb)))
    (fun _ hu => mul_le_mul_of_nonpos_left (le_of_lt hu) hRrate)
  have hsplit : Ioi (0:ℝ) \ Icc a (b*a) = Ioo 0 a ∪ Ioi (b*a) := by
    ext u; simp only [mem_sdiff, mem_Ioi, mem_Icc, mem_union, mem_Ioo]; grind
  have hdis : Disjoint (Ioo 0 a) (Ioi (b*a)) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    exact (not_lt_of_ge (hba.le.trans (le_of_lt hv))) hu.2
  have hm0 : 0 ≤ M := (abs_nonneg (g 0)).trans (by simpa using hM 0 le_rfl)
  have hsav := floor_savings hh hb hσ ha
  change IntegrableOn f _ ∧ (∫ u in _, f u) ≤ _
  rw [hsplit]
  refine ⟨hL.1.union hR.1, ?_⟩
  rw [setIntegral_union hdis measurableSet_Ioi hL.1 hR.1]
  calc
    _ ≤ _ := add_le_add hL.2 hR.2
    _ ≤ M * (σ⁻¹ ^ k * (exp (-(σ*(h*log h-h+1)-2)*a)/σ)) +
        M * (σ⁻¹ ^ k * (b/(h*σ)*exp (-(σ*(b-h-h*log (b/h))-2*b)*a))) := by
      simpa only [k, mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left hsav.1 hm0)
        (mul_le_mul_of_nonneg_left hsav.2 hm0)
    _ = _ := by dsimp [k]; ring

/-- For every shape `1 < h < b`, the two decay coefficients simultaneously exceed any prescribed
threshold at all sufficiently large rates. At each admissible rate the same explicit estimate
holds for every positive cutoff and every measurable input bounded by `M * exp (2*u)`. -/
theorem adjustable_window_off_mass {h b : ℝ} (hh : 1 < h) (hb : h < b) :
    let L := fun σ : ℝ => σ*(h*log h-h+1)-2
    let R := fun σ : ℝ => σ*(b-h-h*log (b/h))-2*b
    (∀ T : ℝ, ∀ᶠ σ : ℝ in Filter.atTop, 2 < σ*(1-h/b) ∧ T < L σ ∧ T < R σ) ∧
    ∀ {σ : ℝ}, 2 < σ*(1-h/b) → ∀ {a : ℝ}, 0 < a → ∀ {g : ℝ → ℝ}, Measurable g →
      ∀ {M : ℝ}, (∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)) →
      let k := ⌊σ*h*a⌋₊
      let f := fun u : ℝ => |g u| * (u ^ k * exp (-(σ*u)) / k.factorial)
      let S := Ioi (0:ℝ) \ Icc a (b*a)
      IntegrableOn f S ∧ (∫ u in S, f u) ≤ M * σ⁻¹ ^ k *
        (exp (-L σ*a) / σ + b/(h*σ)*exp (-R σ*a)) :=
  by
  refine ⟨decay_rates hh hb, ?_⟩
  intro σ hsign a ha g hg M hM
  have hb0 : 0 < b := by linarith
  have hfactor : 0 < 1 - h/b := sub_pos.2 ((div_lt_one hb0).2 hb)
  have hσ : 0 < σ := pos_of_mul_pos_left (by linarith : 0 < σ*(1-h/b)) hfactor.le
  exact mass_at_rate hh hb hσ hsign ha hg hM

end D5.S3.Analytic.Laplace.CriticalGammaWindow
