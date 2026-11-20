/- GID: D5/S3/Analytic/OriginalHalfBinomialPfaffNome
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialPfaffNome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Convex]
   utility: none
   digest: The literal Pfaff jumps and the negative-real continuation of the original nome. -/

import D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
import Mathlib.Analysis.Complex.Convex

/-! Pfaff jumps for the Euler period ratio and their signed nome on the negative real chart. -/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped Topology

namespace D5.S3.Analytic.OriginalHalfBinomialPfaffNome

open OriginalHalfBinomialSlitPeriod

private def pfaffMap (r : ℂ) : ℂ := r / (r - 1)

private def complementMap (r : ℂ) : ℂ := (1 - r)⁻¹

private lemma doubleSlit_of_im_ne_zero {r : ℂ} (hr : r.im ≠ 0) : r ∈ doubleSlit :=
  ⟨Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hr)),
    Complex.mem_slitPlane_iff.2 (Or.inr hr)⟩

private lemma one_sub_ne_zero {r : ℂ} (hr : r ∈ doubleSlit) : 1 - r ≠ 0 :=
  Complex.slitPlane_ne_zero hr.1

private lemma pfaffMap_im (r : ℂ) : (pfaffMap r).im = -r.im / normSq (r - 1) := by
  rw [pfaffMap, Complex.div_im]
  simp
  ring

private lemma pfaffMap_mem {r : ℂ} (hr : r.im ≠ 0) : pfaffMap r ∈ doubleSlit :=
  doubleSlit_of_im_ne_zero (by
    rw [pfaffMap_im]
    exact div_ne_zero (neg_ne_zero.mpr hr)
      (normSq_pos.mpr (by intro h; apply hr; simpa using congrArg Complex.im h)).ne')

private lemma complementMap_eq {r : ℂ} (hr : 1 - r ≠ 0) :
    complementMap r = 1 - pfaffMap r := by
  have he : r - 1 = -(1 - r) := by ring
  unfold complementMap pfaffMap
  rw [he, div_neg]
  field_simp
  ring

private lemma complement_tau {r : ℂ} (hr : r ∈ doubleSlit) :
    tau (1 - r) = -(tau r)⁻¹ := by
  have hp := slitPeriod_ne_zero hr.1
  have hq : slitPeriod (1 - r) ≠ 0 :=
    slitPeriod_ne_zero (by simpa [slitDomain] using hr.2)
  simp only [tau, sub_sub_cancel]
  field_simp [I_ne_zero]
  rw [Complex.I_sq]

private def tauDerivative (r : ℂ) : ℂ :=
  -Complex.I / ((Real.pi : ℂ) * r * (1 - r) * slitPeriod r ^ 2)

private lemma tauDerivative_ne_zero {r : ℂ} (hr : r ∈ doubleSlit) :
    tauDerivative r ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr I_ne_zero) <|
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        (Complex.slitPlane_ne_zero hr.2)) (one_sub_ne_zero hr))
      (pow_ne_zero 2 (slitPeriod_ne_zero hr.1))

private lemma pfaffMap_hasDerivAt {r : ℂ} (hr : 1 - r ≠ 0) :
    HasDerivAt pfaffMap (-(1 - r)⁻¹ ^ 2) r := by
  have he : r - 1 = -(1 - r) := by ring
  unfold pfaffMap
  convert (hasDerivAt_id r).fun_div ((hasDerivAt_id r).sub_const 1)
    (he ▸ neg_ne_zero.mpr hr) using 1 <;> try rfl
  change -(1 - r)⁻¹ ^ 2 = ((1 : ℂ) * (r - 1) - r * 1) / (r - 1) ^ 2
  rw [show (1 : ℂ) * (r - 1) - r * 1 = -1 by ring,
    he, neg_sq, div_eq_mul_inv, ← inv_pow, neg_one_mul]

private lemma pfaff_period_sq {r : ℂ} (hr : r ∈ doubleSlit) :
    slitPeriod (pfaffMap r) ^ 2 = (1 - r) * slitPeriod r ^ 2 := by
  change slitPeriod (r / (r - 1)) ^ 2 = _
  rw [pfaff hr.1, mul_pow, ← Complex.cpow_nat_mul]
  norm_num

private lemma tau_pfaff_hasDerivAt {r : ℂ} (hr : r.im ≠ 0) :
    HasDerivAt (fun z => tau (pfaffMap z)) (tauDerivative r) r := by
  have hd := doubleSlit_of_im_ne_zero hr
  have h₀ := Complex.slitPlane_ne_zero hd.2
  have h₁ := one_sub_ne_zero hd
  have hp := slitPeriod_ne_zero hd.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  convert (tau_hasDerivAt (pfaffMap_mem hr)).comp r (pfaffMap_hasDerivAt h₁) using 1 <;> try rfl
  rw [pfaff_period_sq hd, ← complementMap_eq h₁]
  have he : r - 1 = -(1 - r) := by ring
  simp only [tauDerivative, pfaffMap, complementMap, he, div_neg]
  field_simp

private lemma tau_pfaff_difference_hasDerivAt {r : ℂ} (hr : r.im ≠ 0) :
    HasDerivAt (fun z => tau z - tau (pfaffMap z)) 0 r := by
  have ht : HasDerivAt tau (tauDerivative r) r := tau_hasDerivAt (doubleSlit_of_im_ne_zero hr)
  simpa only [sub_self] using ht.fun_sub (tau_pfaff_hasDerivAt hr)

private lemma tau_nonzero {r : ℂ} (hr : r ∈ doubleSlit) : tau r ≠ 0 := by
  intro h
  simpa [h] using tau_im_pos hr

private lemma upper_difference_constant :
    ∃ c : ℂ, ∀ r : ℂ, 0 < r.im → tau r - tau (pfaffMap r) = c := by
  have ho : IsOpen {r : ℂ | 0 < r.im} := isOpen_lt continuous_const Complex.continuous_im
  exact ho.exists_is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
    (fun _ hr =>
      (tau_pfaff_difference_hasDerivAt (ne_of_gt hr)).differentiableAt.differentiableWithinAt)
    (fun _ hr => (tau_pfaff_difference_hasDerivAt (ne_of_gt hr)).deriv)

private lemma upper_difference_value {c : ℂ}
    (hc : ∀ r : ℂ, 0 < r.im → tau r - tau (pfaffMap r) = c) : c = 1 := by
  let a : ℝ := Real.sqrt 3
  have ha : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have ha₂ : a ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  let u : ℂ := (1 + I * (a : ℂ)) / 2
  have huim : 0 < u.im := by
    change 0 < ((1 + I * (a : ℂ)) / 2).im
    simpa [Complex.div_im] using (show 0 < a / 2 by positivity)
  have hu : u ∈ doubleSlit := doubleSlit_of_im_ne_zero huim.ne'
  have hu₂ : u ^ 2 - u + 1 = 0 := by
    have hcast : (a : ℂ) ^ 2 = 3 := by exact_mod_cast ha₂
    dsimp [u]
    linear_combination (norm := ring_nf)
      -(1 / 4 : ℂ) * hcast + (a : ℂ) ^ 2 / 4 * Complex.I_sq
  have hfix : complementMap u = u := by
    rw [complementMap, ← one_div]
    apply (div_eq_iff (one_sub_ne_zero hu)).2
    linear_combination hu₂
  have hrelation (r : ℂ) (hr : 0 < r.im) :
      tau (complementMap r) = -(tau r - c)⁻¹ := by
    rw [complementMap_eq (one_sub_ne_zero (doubleSlit_of_im_ne_zero hr.ne')),
      complement_tau (pfaffMap_mem hr.ne')]
    have he := hc r hr
    rw [show tau r - c = tau (pfaffMap r) by linear_combination he]
  have hvalue : tau u = -(tau u - c)⁻¹ := by simpa only [hfix] using hrelation u huim
  have hden : tau u - c ≠ 0 := by
    rw [show tau u - c = tau (pfaffMap u) by linear_combination hc u huim]
    exact tau_nonzero (pfaffMap_mem huim.ne')
  have hG : HasDerivAt complementMap (u ^ 2) u := by
    have h := ((hasDerivAt_id u).const_sub 1).fun_inv (one_sub_ne_zero hu)
    have he : (1 - u)⁻¹ ^ 2 = u ^ 2 := congrArg (fun z : ℂ => z ^ 2) hfix
    unfold complementMap
    convert h using 1 <;> try rfl
    change u ^ 2 = -(-1 : ℂ) / (1 - u) ^ 2
    rw [neg_neg, one_div, ← inv_pow, he]
  have ht : HasDerivAt tau (tauDerivative u) u := tau_hasDerivAt hu
  have hL : HasDerivAt (fun z => tau (complementMap z)) (tauDerivative u * u ^ 2) u := by
    have h' : HasDerivAt tau (tauDerivative u) (complementMap u) := by simpa only [hfix] using ht
    exact h'.comp u hG
  have hR : HasDerivAt (fun z => -(tau z - c)⁻¹) (tauDerivative u * tau u ^ 2) u := by
    convert ((ht.sub_const c).inv hden).neg using 1
    rw [show tau u ^ 2 = ((tau u - c)⁻¹) ^ 2 by nth_rw 1 [hvalue]; ring]
    simp [div_eq_mul_inv, inv_pow]
  have ho : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hevent : (fun z => tau (complementMap z)) =ᶠ[𝓝 u] (fun z => -(tau z - c)⁻¹) := by
    filter_upwards [ho.mem_nhds huim] with z hz
    exact hrelation z hz
  have hsq := mul_left_cancel₀ (tauDerivative_ne_zero hu)
    (hL.unique (hR.congr_of_eventuallyEq hevent))
  have hτu : tau u = u := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq.symm with h | h
    · exact h
    · have him := tau_im_pos hu
      rw [h, Complex.neg_im] at him
      linarith
  rw [hτu] at hvalue hden
  have he : u * (u - c) = -1 := by
    rw [eq_neg_iff_add_eq_zero] at hvalue
    field_simp at hvalue
    linear_combination hvalue
  have hn : u ≠ 0 := Complex.slitPlane_ne_zero hu.2
  apply mul_left_cancel₀ hn
  linear_combination hu₂ - he

/-- The exact upper-half-plane jump of the original complementary ratio. -/
theorem tau_pfaff_upper {r : ℂ} (hr : 0 < r.im) :
    tau r = tau (r / (r - 1)) + 1 := by
  obtain ⟨c, hc⟩ := upper_difference_constant
  change tau r = tau (pfaffMap r) + 1
  have he := hc r hr
  rw [upper_difference_value hc] at he
  linear_combination he

/-- The exact lower-half-plane jump of the original complementary ratio. -/
theorem tau_pfaff_lower {r : ℂ} (hr : r.im < 0) :
    tau r = tau (r / (r - 1)) - 1 := by
  have hden : 1 - r ≠ 0 := one_sub_ne_zero (doubleSlit_of_im_ne_zero hr.ne)
  have hpositive : 0 < (pfaffMap r).im := by
    rw [pfaffMap_im]
    exact div_pos (neg_pos.mpr hr) (normSq_pos.mpr (by
      have he : r - 1 = -(1 - r) := by ring
      exact he ▸ neg_ne_zero.mpr hden))
  have hinv : pfaffMap (pfaffMap r) = r := by
    have he : pfaffMap r - 1 = -(1 - r)⁻¹ := by
      change pfaffMap r - 1 = -complementMap r
      rw [complementMap_eq hden]
      ring
    conv_lhs => unfold pfaffMap
    change pfaffMap r / (pfaffMap r - 1) = r
    rw [he]
    unfold pfaffMap
    have hsub : r - 1 = -(1 - r) := by ring
    rw [hsub]
    field_simp
  have hj := tau_pfaff_upper hpositive
  change tau (pfaffMap r) = tau (pfaffMap (pfaffMap r)) + 1 at hj
  rw [hinv] at hj
  change tau r = tau (pfaffMap r) - 1
  linear_combination -hj

/-- The signed Pfaff expression giving the original nome through the negative real cut. -/
def negativeChartNome (r : ℂ) : ℂ :=
  -Complex.exp (Complex.I * (Real.pi : ℂ) * tau (r / (r - 1)))

private lemma nome_eq_negativeChartNome {r : ℂ} (hr : r.im ≠ 0) :
    Complex.exp (Complex.I * (Real.pi : ℂ) * tau r) = negativeChartNome r := by
  have hπ : Complex.exp (I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have hnπ : Complex.exp (-(I * (Real.pi : ℂ))) = -1 := by
    rw [mul_comm I, Complex.exp_neg_pi_mul_I]
  rcases lt_or_gt_of_ne hr with hn | hp
  · rw [tau_pfaff_lower hn, mul_sub, mul_one, sub_eq_add_neg, Complex.exp_add, hnπ]
    simp [negativeChartNome]
  · rw [tau_pfaff_upper hp, mul_add, mul_one, Complex.exp_add, hπ]
    simp [negativeChartNome]

private lemma tau_analyticAt {r : ℂ} (hr : r ∈ doubleSlit) : AnalyticAt ℂ tau r := by
  have hc : 1 - r ∈ slitDomain := by simpa [slitDomain] using hr.2
  have h := (slitPeriod_analyticOnNhd _ hc).comp (analyticAt_const.sub analyticAt_id)
  exact (analyticAt_const.mul h).div (slitPeriod_analyticOnNhd _ hr.1) (slitPeriod_ne_zero hr.1)

private lemma pfaffMap_real_mem {x : ℝ} (hx : x < 0) :
    pfaffMap (x : ℂ) ∈ doubleSlit := by
  have he : pfaffMap (x : ℂ) = ((x / (x - 1) : ℝ) : ℂ) := by push_cast; rfl
  have hp : 0 < x / (x - 1) := div_pos_of_neg_of_neg hx (by linarith)
  have hlt : x / (x - 1) < 1 :=
    (div_lt_iff_of_neg (by linarith : x - 1 < 0)).2 (by linarith)
  rw [he]
  refine ⟨Complex.mem_slitPlane_iff.2 (Or.inl ?_), Complex.mem_slitPlane_iff.2 (Or.inl ?_)⟩
  · rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  · rwa [Complex.ofReal_re]

/-- A single signed nome and all its natural powers extend across each negative real point. -/
theorem negative_real_nome_extension (x : ℝ) (hx : x < 0) :
    ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧
      AnalyticOnNhd ℂ negativeChartNome U ∧
      (∀ z ∈ U, ‖negativeChartNome z‖ < 1) ∧
      (∀ z ∈ U ∩ doubleSlit,
        negativeChartNome z = Complex.exp (Complex.I * (Real.pi : ℂ) * tau z)) ∧
      ∀ m : ℕ, AnalyticOnNhd ℂ (fun z => negativeChartNome z ^ m) U ∧
        (∀ z ∈ U ∩ doubleSlit,
          negativeChartNome z ^ m = Complex.exp (Complex.I * (Real.pi : ℂ) * tau z) ^ m) ∧
        ∀ z ∈ U, negativeChartNome z ^ m =
          (-1 : ℂ) ^ m * Complex.exp (Complex.I * (Real.pi : ℂ) * tau (z / (z - 1))) ^ m := by
  let U : Set ℂ := {z : ℂ | z ≠ 1 ∧ 0 > z.re ∧ pfaffMap z ∈ doubleSlit}
  have hOpen : IsOpen doubleSlit :=
    (Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).inter
      Complex.isOpen_slitPlane
  have hne {z : ℂ} (hz : z ∈ U) : 1 - z ≠ 0 := sub_ne_zero.mpr hz.1.symm
  have hup {z : ℂ} (hz : z ∈ U) : ContinuousAt pfaffMap z :=
    (pfaffMap_hasDerivAt (hne hz)).continuousAt
  have hneOpen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hleft : IsOpen {z : ℂ | z.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.2
    intro z hz
    filter_upwards [hneOpen.mem_nhds hz.1, hleft.mem_nhds hz.2.1,
      (hup hz).eventually_mem (hOpen.mem_nhds hz.2.2)] with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hxU : (x : ℂ) ∈ U := by
    refine ⟨?_, by simpa using hx, pfaffMap_real_mem hx⟩
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith
  have han : AnalyticOnNhd ℂ negativeChartNome U := by
    intro z hz
    have hs : AnalyticAt ℂ pfaffMap z :=
      analyticAt_id.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hz.1)
    exact (analyticAt_const.mul ((tau_analyticAt hz.2.2).comp hs)).cexp'.neg
  have hmatch (z : ℂ) (hz : z ∈ U ∩ doubleSlit) :
      negativeChartNome z = Complex.exp (Complex.I * (Real.pi : ℂ) * tau z) := by
    exact (nome_eq_negativeChartNome
      ((Complex.mem_slitPlane_iff.mp hz.2.2).resolve_left hz.1.2.1.not_gt)).symm
  refine ⟨U, hU, hxU, han, ?_, hmatch, ?_⟩
  · intro z hz
    rw [negativeChartNome, norm_neg, Complex.norm_exp, Real.exp_lt_one_iff]
    change (I * (Real.pi : ℂ) * tau (pfaffMap z)).re < 0
    simpa [Complex.mul_re, Complex.mul_im] using
      (neg_neg_of_pos (mul_pos Real.pi_pos (tau_im_pos hz.2.2)))
  · intro m
    exact ⟨fun z hz => (han z hz).pow m, fun z hz => congrArg (· ^ m) (hmatch z hz),
      fun z _ => by simp only [negativeChartNome, ← mul_pow, neg_one_mul]⟩

end D5.S3.Analytic.OriginalHalfBinomialPfaffNome
