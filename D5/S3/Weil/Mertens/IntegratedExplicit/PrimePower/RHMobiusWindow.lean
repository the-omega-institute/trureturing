/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform all-orders prime-only window expansion under RH. -/

import Mathlib.NumberTheory.Harmonic.Bounds
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff

/-! Möbius truncation, actual root spectra and one common threshold for the prime window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real ArithmeticFunction MeasureTheory Set
open scoped ArithmeticFunction.Moebius
open Finset (sum_congr sum_le_sum)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.IntegratedExplicit
open RHSharpActualEnvelope (abs_G_sub_normalized_actualH_le on_line)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

open D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity (finite_error_integral normalized_error_integral)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G_split_nonneg)
open D5.S3.Weil.Mertens.ZeroAbscissaPower (actual_low_weight actual_high_weight)

private theorem q_from_one {x : ℝ} (hx : 1 ≤ x) : U x / x = -Q x := by
  have hK := chebyshev_error_kernel_integrable
  have htail : IntegrableOn K (Ioi x) := hK.mono_set (Ioi_subset_Ioi hx)
  have hs := intervalIntegral.integral_interval_add_Ioi hK htail
  rw [finite_error_integral hK hx, normalized_error_integral hK] at hs
  change _ + Q x = _ at hs
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  unfold U
  field_simp [hx₀.ne']
  field_simp [hx₀.ne'] at hs
  linarith only [hs]

private theorem q_error_formula_from_one {x : ℝ} (hx : 1 ≤ x) :
    qError x = (trivialT (Real.log x) - Real.log (2 * Real.pi)) / x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hs := G_split_nonneg (Real.log_nonneg hx)
  rw [RHSharpActualEnvelope.G, Real.exp_log hx₀] at hs
  change Real.exp (-Real.log x / 2) * U x =
    ((Real.exp (-Real.log x / 2) : ℝ) * actualH (Real.log x)).re +
      Real.exp (-Real.log x / 2) * (Real.log (2 * Real.pi) - trivialT (Real.log x)) at hs
  rw [Complex.re_ofReal_mul] at hs
  rw [← mul_add] at hs
  have hU := (mul_left_cancel₀ (Real.exp_pos _).ne') hs
  have hQ := q_from_one hx
  unfold qError
  rw [zeroTail_eq, Complex.re_ofReal_mul, Real.exp_neg, Real.exp_log hx₀]
  rw [hU] at hQ
  rw [add_div] at hQ
  simp only [div_eq_mul_inv] at hQ ⊢
  linear_combination hQ


private def trivialHeight (k : ℕ) : ℝ := 2 * ((k : ℝ) + 1)

private theorem trivial_weighted_tail {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    HasSum (fun k : ℕ => trivialCoeff k * Real.exp (-(r + trivialHeight k) * v) / (r + trivialHeight k))
      (∫ u in Ioi v, Real.exp (-r * u) * trivialT u) := by
  let f (k : ℕ) (u : ℝ) := trivialCoeff k * Real.exp (-(r + trivialHeight k) * u)
  let b (k : ℕ) (u : ℝ) := trivialCoeff k * Real.exp (-r * u)
  have H : HasSum (fun k : ℕ => ∫ u in Ioi v, f k u)
      (∫ u in Ioi v, Real.exp (-r * u) * trivialT u) := by
    apply hasSum_integral_of_dominated_convergence b
    · intro k
      exact (show Continuous (f k) by unfold f; fun_prop).aestronglyMeasurable
    · intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := hv.trans hu.le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (trivialCoeff_nonneg k) (Real.exp_nonneg _))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have hh : 0 ≤ trivialHeight k := by unfold trivialHeight; positivity
        nlinarith [mul_nonneg hh hu0])) (trivialCoeff_nonneg k)
    · exact ae_of_all _ fun u => trivialCoeff_hasSum.summable.mul_right _
    · simpa only [b, tsum_mul_right, trivialCoeff_hasSum.tsum_eq] using
        (integrableOn_exp_mul_Ioi (a := -r) (by linarith) v).const_mul (1 - Real.log 2)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have H := (trivialT_summable (hv.trans hu.le)).hasSum.mul_left (Real.exp (-r * u))
      convert H using 1
      · funext k
        dsimp only [f, trivialHeight]
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      · rfl
  convert H using 1
  funext k
  have hh : 0 < trivialHeight k := by unfold trivialHeight; positivity
  rw [show (∫ u in Ioi v, f k u) = trivialCoeff k *
      (∫ u in Ioi v, Real.exp (-(r + trivialHeight k) * u)) by
    exact integral_const_mul ..,
    integral_exp_mul_Ioi (by linarith), div_neg, neg_div, neg_neg, mul_div_assoc]

private theorem trivial_mode_bound (n : ℕ) :
    (∑' k : ℕ, (n : ℝ) / (trivialHeight k * ((n : ℝ) + trivialHeight k))) ≤
      (1 + Real.log n) / 2 := by
  let g (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹
  refine Real.tsum_le_of_sum_range_le (fun k => by unfold trivialHeight; positivity) (fun L => ?_)
  have hp (k : ℕ) : (n : ℝ) / (trivialHeight k * ((n : ℝ) + trivialHeight k)) ≤
      (g k - g (k + n)) / 2 := by
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hn : (0 : ℝ) ≤ n := by positivity
    unfold g trivialHeight
    push_cast
    have hd : 0 < (k : ℝ) + 1 + n := by positivity
    have hid : ((k : ℝ) + 1)⁻¹ - ((k : ℝ) + n + 1)⁻¹ =
        (n : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + n + 1)) := by
      field_simp
      ring
    rw [hid, div_div]
    apply div_le_div_of_nonneg_left hn (by positivity)
    nlinarith [mul_nonneg hk.le hk.le]
  have hcancel :
      (∑ k ∈ Finset.range L, (g k - g (k + n)) / 2) =
        ((∑ k ∈ Finset.range n, g k) - ∑ k ∈ Finset.range n, g (k + L)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    have ha := Finset.sum_range_add g n L
    have hb := Finset.sum_range_add g L n
    simp_rw [add_comm n] at ha
    simp_rw [add_comm L] at hb
    rw [Nat.add_comm n L] at hb
    linarith only [ha, hb]
  have hh : (∑ k ∈ Finset.range n, g k) = (harmonic n : ℝ) := by
    simp [g, harmonic, Rat.cast_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range L, (g k - g (k + n)) / 2 :=
      Finset.sum_le_sum fun k _ => hp k
    _ = _ := hcancel
    _ ≤ _ := by
      rw [hh]
      have hpos : 0 ≤ ∑ k ∈ Finset.range n, g (k + L) :=
        Finset.sum_nonneg fun k _ => by unfold g; positivity
      linarith [harmonic_le_one_add_log n]


private theorem q_weighted_transport {r v : ℝ} (hr : 1 < r) (hv : 0 ≤ v) :
    IntegrableOn (fun t => t ^ (-r) * qError t) (Ioi (Real.exp v)) ∧
    r * Real.exp v * (qError (Real.exp v) - (r - 1) * Real.exp ((r - 1) * v) *
      (∫ t in Ioi (Real.exp v), t ^ (-r) * qError t)) =
    (∑' k : ℕ, (r / (trivialHeight k * (r + trivialHeight k))) * Real.exp (-(trivialHeight k) * v)) -
      Real.log (2 * Real.pi) := by
  have hr₀ : 0 < r := by linarith
  let l := Real.log (2 * Real.pi)
  let e := Real.exp (r * v)
  let f (t : ℝ) := t ^ (-r) * qError t
  have htransform (u : ℝ) (hu : u ∈ Ioi v) :
      Real.exp u • f (Real.exp u) = Real.exp (-r * u) * (trivialT u - l) := by
    have hu₀ := hv.trans hu.le
    dsimp only [f, smul_eq_mul]
    rw [q_error_formula_from_one (Real.one_le_exp_iff.mpr hu₀), Real.log_exp, ← Real.exp_mul]
    rw [mul_comm u (-r)]
    field_simp [ne_of_gt (Real.exp_pos u)]
    rfl
  have hconst : IntegrableOn (fun u => Real.exp (-r * u) * l) (Ioi v) :=
    (integrableOn_exp_mul_Ioi (a := -r) (by linarith) v).mul_const l
  have htriv : IntegrableOn (fun u => Real.exp (-r * u) * trivialT u) (Ioi v) := by
    apply ((integrableOn_exp_mul_Ioi (a := -r) (by linarith) v).mul_const
      (1 - Real.log 2)).mono'
    · exact ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-r * u))).continuousOn.mul
        (trivialT_continuousOn.mono (fun _ hu => hv.trans hu.le))).aestronglyMeasurable
          measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu₀ := hv.trans hu.le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (trivialT_nonneg hu₀))]
      exact mul_le_mul_of_nonneg_left (trivialT_le_mass hu₀) (Real.exp_nonneg _)
  have hdiff : IntegrableOn (fun u => Real.exp (-r * u) * (trivialT u - l)) (Ioi v) := by
    simp_rw [mul_sub]
    exact htriv.sub hconst
  have hsub : IntegrableOn (fun u => Real.exp u • f (Real.exp u)) (Ioi v) := by
    apply hdiff.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using (htransform u hu).symm
  refine ⟨(integrableOn_comp_exp_Ioi f v).mp hsub, ?_⟩
  let I := ∫ u in Ioi v, Real.exp (-r * u) * trivialT u
  have const_eval : (∫ u in Ioi v, Real.exp (-r * u) * l) = l * e⁻¹ / r := by
    rw [integral_mul_const, integral_exp_mul_Ioi (by linarith)]
    dsimp only [e]
    rw [neg_mul, Real.exp_neg, div_neg, neg_div, neg_neg]
    ring
  rw [show (∫ t in Ioi (Real.exp v), t ^ (-r) * qError t) = I - l * e⁻¹ / r by
    change (∫ t in Ioi (Real.exp v), f t) = _
    rw [← integral_comp_exp_Ioi f v, ← const_eval, ← integral_sub htriv hconst]
    exact setIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [htransform u hu, mul_sub]]
  rw [q_error_formula_from_one (Real.one_le_exp_iff.mpr hv), Real.log_exp]
  have hmul : Real.exp v * Real.exp ((r - 1) * v) = e := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : e ≠ 0 := (Real.exp_pos _).ne'
  have habsorb : r * Real.exp v * ((trivialT v - l) / Real.exp v -
      (r - 1) * Real.exp ((r - 1) * v) * (I - l * e⁻¹ / r)) =
      r * (trivialT v - (r - 1) * e * I) - l := by
    rw [show r * Real.exp v * ((trivialT v - l) / Real.exp v -
        (r - 1) * Real.exp ((r - 1) * v) * (I - l * e⁻¹ / r)) =
      r * ((trivialT v - l) - (r - 1) * (Real.exp v * Real.exp ((r - 1) * v)) *
        (I - l * e⁻¹ / r)) by field_simp, hmul]
    field_simp
    ring
  rw [habsorb]
  change _ = _ - l
  congr 1
  have hsum := (((trivialT_summable hv).hasSum.sub
    ((trivial_weighted_tail hr₀ hv).mul_left ((r - 1) * e))).mul_left r)
  change HasSum _ (r * (trivialT v - (r - 1) * e * I)) at hsum
  rw [← hsum.tsum_eq]
  apply tsum_congr
  intro k
  have hexp : e * Real.exp (-(r + trivialHeight k) * v) = Real.exp (-(trivialHeight k) * v) := by
    unfold e
    rw [← Real.exp_add]
    congr 1
    ring
  have hk : 0 < trivialHeight k := by unfold trivialHeight; positivity
  rw [show (r - 1) * e * (trivialCoeff k * Real.exp (-(r + trivialHeight k) * v) /
      (r + trivialHeight k)) = (r - 1) * trivialCoeff k * (e * Real.exp (-(r + trivialHeight k) * v)) /
      (r + trivialHeight k) by ring, hexp]
  change r * (trivialCoeff k * Real.exp (-(trivialHeight k) * v) - _) = _
  change r * ((1 / (trivialHeight k * (trivialHeight k + 1))) * Real.exp (-(trivialHeight k) * v) - _) = _
  change r * ((1 / (trivialHeight k * (trivialHeight k + 1))) * Real.exp (-(trivialHeight k) * v) -
    (r - 1) * (1 / (trivialHeight k * (trivialHeight k + 1))) * Real.exp (-(trivialHeight k) * v) /
      (r + trivialHeight k)) = _
  field_simp
  ring


private def trivialConstant : ℝ := 1 + |Real.log (2 * Real.pi)|

private theorem q_weighted_log_bound {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 ≤ v) :
    |(n : ℝ) * Real.exp v * (qError (Real.exp v) - ((n : ℝ) - 1) * Real.exp (((n : ℝ) - 1) * v) *
      (∫ t in Ioi (Real.exp v), t ^ (-(n : ℝ)) * qError t))| ≤
    trivialConstant * (1 + Real.log n) := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) < n := by linarith
  rw [(q_weighted_transport hn₁ hv).2]
  let c (k : ℕ) := (n : ℝ) / (trivialHeight k * ((n : ℝ) + trivialHeight k))
  have hc (k : ℕ) : 0 ≤ c k := by unfold c trivialHeight; positivity
  have hmajor (k : ℕ) : c k ≤ (n : ℝ) * trivialCoeff k := by
    change (n : ℝ) / (trivialHeight k * ((n : ℝ) + trivialHeight k)) ≤
      (n : ℝ) * (1 / (trivialHeight k * (trivialHeight k + 1)))
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by positivity) (by unfold trivialHeight; positivity)
    apply mul_le_mul_of_nonneg_left (by linarith) (by unfold trivialHeight; positivity)
  have hs : Summable c := Summable.of_nonneg_of_le hc hmajor
    (trivialCoeff_hasSum.summable.mul_left (n : ℝ))
  let f (k : ℕ) := c k * Real.exp (-(trivialHeight k) * v)
  have hf (k : ℕ) : 0 ≤ f k := mul_nonneg (hc k) (Real.exp_nonneg _)
  have hle (k : ℕ) : f k ≤ c k := by
    have hheight : 0 ≤ trivialHeight k := by unfold trivialHeight; positivity
    exact mul_le_of_le_one_right (hc k)
      (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hheight hv]))
  have ht := (Summable.of_nonneg_of_le hf hle hs).tsum_le_tsum hle hs
  have hh := ht.trans (trivial_mode_bound n)
  change |(∑' k, f k) - Real.log (2 * Real.pi)| ≤ _
  have hnlog := Real.log_nonneg hn₁.le
  calc
    _ ≤ |∑' k, f k| + |Real.log (2 * Real.pi)| := abs_sub _ _
    _ ≤ (1 + Real.log n) / 2 + |Real.log (2 * Real.pi)| := by
      rw [abs_of_nonneg (tsum_nonneg hf)]
      exact add_le_add hh le_rfl
    _ ≤ _ := by
      unfold trivialConstant
      nlinarith [abs_nonneg (Real.log (2 * Real.pi)),
        mul_nonneg (abs_nonneg (Real.log (2 * Real.pi))) hnlog]


private theorem root_coeff_low_majorant (hRH : RiemannHypothesis) {r : ℝ}
    (hr : 2 ≤ r) (k : ℕ) :
    ‖rootCoeff r k‖ ≤ 2 * (1 / ‖actualZero k‖) := by
  have hr₀ : 0 < r := by linarith
  have hρ₀ : 0 < ‖actualZero k‖ := norm_pos_iff.mpr (by
    intro h
    have hl := on_line hRH k
    rw [h, Complex.zero_re] at hl
    norm_num at hl)
  have hRe := Complex.abs_re_le_norm ((r : ℂ) - actualZero k)
  rw [Complex.sub_re, Complex.ofReal_re, on_line hRH k, abs_of_nonneg (by linarith)] at hRe
  have hrhalf : r / 2 ≤ ‖(r : ℂ) - actualZero k‖ := by linarith
  have hdiff₀ : 0 < ‖(r : ℂ) - actualZero k‖ := (by linarith : 0 < r / 2).trans_le hrhalf
  unfold rootCoeff
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀, norm_mul]
  calc
    _ ≤ r / (‖actualZero k‖ * (r / 2)) := by
      exact div_le_div_of_nonneg_left hr₀.le (by positivity)
        (mul_le_mul_of_nonneg_left hrhalf hρ₀.le)
    _ = _ := by field_simp

private theorem root_coeff_high_majorant {r : ℝ} (hr : 2 ≤ r) (k : ℕ)
    (hk : r < |(actualZero k).im|) :
    ‖rootCoeff r k‖ ≤ r * ((actualZero k).im)⁻¹ ^ 2 := by
  have hr₀ : 0 < r := by linarith
  have him₀ : 0 < |(actualZero k).im| := hr₀.trans hk
  have ha := Complex.abs_im_le_norm (actualZero k)
  have hb : |(actualZero k).im| ≤ ‖(r : ℂ) - actualZero k‖ := by
    simpa using Complex.abs_im_le_norm ((r : ℂ) - actualZero k)
  unfold rootCoeff
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀, norm_mul]
  calc
    _ ≤ r / (|(actualZero k).im| * |(actualZero k).im|) :=
      div_le_div_of_nonneg_left hr₀.le (mul_pos him₀ him₀)
        (mul_le_mul ha hb him₀.le (norm_nonneg _))
    _ = _ := by rw [← sq, sq_abs, inv_pow, div_eq_mul_inv]

private theorem root_coeff_mass_bound (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 2 ≤ r →
      Summable (fun k : ℕ => ‖rootCoeff r k‖) ∧
        (∑' k : ℕ, ‖rootCoeff r k‖) ≤ C * (1 + Real.log r)^2 := by
  obtain ⟨A, hA, hlow⟩ := actual_low_weight
  obtain ⟨B, hB, hhigh⟩ := actual_high_weight
  refine ⟨2 * A + B + 1, by positivity, ?_⟩
  intro r hr
  have hr₀ : 0 < r := by linarith
  let low (k : ℕ) := if |(actualZero k).im| ≤ r then 1 / ‖actualZero k‖ else 0
  let high (k : ℕ) := if r < |(actualZero k).im| then ((actualZero k).im)⁻¹ ^ 2 else 0
  have hl : Summable low := (hlow r hr).1
  have hinv : Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
    simpa only [Function.comp_def, actualZero] using
      actualOccurrenceEquiv.summable_iff.mpr actual_sigma_inverse_square_summable
  have hh : Summable high := Summable.of_nonneg_of_le (fun k => by unfold high; positivity)
    (fun k => by
      unfold high
      split_ifs
      · exact le_rfl
      · positivity) hinv
  let majorant (k : ℕ) := 2 * low k + r * high k
  have hsum : Summable majorant := (hl.mul_left (2 : ℝ)).add (hh.mul_left r)
  have hpoint (k : ℕ) : ‖rootCoeff r k‖ ≤ 2 * low k + r * high k := by
    by_cases hk : |(actualZero k).im| ≤ r
    · simpa only [low, high, ite_eq_left hk, ite_eq_right (not_lt.mpr hk), mul_zero, add_zero]
        using root_coeff_low_majorant hRH hr k
    · simpa only [low, high, ite_eq_right hk, ite_eq_left (lt_of_not_ge hk), mul_zero, zero_add]
        using root_coeff_high_majorant hr k (lt_of_not_ge hk)
  have hs : Summable (fun k => ‖rootCoeff r k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hsum
  refine ⟨hs, ?_⟩
  have hn : 1 ≤ 1 + Real.log r := by
    linarith [Real.log_nonneg (show 1 ≤ r by linarith)]
  have hsq : 1 + Real.log r ≤ (1 + Real.log r)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ 1 + Real.log r by linarith)]
  have hcompare : (∑' k : ℕ, ‖rootCoeff r k‖) ≤ ∑' k, majorant k :=
    hs.tsum_le_tsum hpoint hsum
  calc
    _ ≤ ∑' k, majorant k := hcompare
    _ = 2 * (∑' k, low k) + r * (∑' k, high k) := by
      unfold majorant
      rw [(hl.mul_left (2 : ℝ)).tsum_add (hh.mul_left r), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * (A * (1 + Real.log r)^2) + r * (B * (1 + Real.log r) / r) :=
      add_le_add (mul_le_mul_of_nonneg_left (hlow r hr).2 (by norm_num))
        (mul_le_mul_of_nonneg_left (hhigh r hr) hr₀.le)
    _ ≤ _ := by
      have he : r * (B * (1 + Real.log r) / r) = B * (1 + Real.log r) := by
        field_simp
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hsq hB, sq_nonneg (1 + Real.log r)]


private theorem root_density_log_sq (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ≥ 2, ∀ u : ℝ,
      |rootDensity r u| ≤ C * (1 + Real.log r)^2 *
        Real.exp (((2 * r)⁻¹ - 1 / 2) * u) := by
  obtain ⟨C, hC, hmass⟩ := root_coeff_mass_bound hRH
  refine ⟨C, hC, fun r hr u => ?_⟩
  obtain ⟨hs, hle⟩ := hmass r hr
  let weight := Real.exp (((2 * r)⁻¹ - 1 / 2) * u)
  have hMode (k : ℕ) : ‖rootMode r u k‖ = ‖rootCoeff r k‖ * weight := by
    have hRe : (actualZero k / (r : ℂ)).re = (2 * r)⁻¹ := by
      simp [Complex.div_re, Complex.normSq_ofReal, on_line hRH k]
      field_simp
    rw [rootMode, norm_mul, Complex.norm_exp, mul_comm _ (u : ℂ), Complex.re_ofReal_mul,
      Complex.sub_re, hRe]
    have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
    rw [hhalf, mul_comm u]
  change |(∑' k, rootMode r u k).re| ≤ _ * weight
  exact ((Complex.abs_re_le_norm _).trans
    (tsum_of_norm_bounded (hs.hasSum.mul_right weight) (fun k => (hMode k).le))).trans
    (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))


private theorem root_centered_log_bound {n : ℕ} (hn : 2 ≤ n)
    {v : ℝ} (hv : 0 ≤ v) :
    |centered (n : ℝ) (Real.exp ((n : ℝ) * v)) - rootDensity (n : ℝ) ((n : ℝ) * v)| ≤
      trivialConstant * (1 + Real.log n) * Real.exp (-((n : ℝ) * v) / 2) := by
  let r := (n : ℝ)
  have hr : 1 < r := by dsimp [r]; exact_mod_cast (show 1 < n by omega)
  let y := Real.exp v
  let x := Real.exp (r * v)
  let s := Real.exp ((1 - r / 2) * v)
  let w := Real.exp ((r - 1) * v)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := (Real.exp_zero : Real.exp (0 : ℝ) = 1) ▸
    Real.exp_le_exp.mpr (mul_nonneg hr0.le hv)
  have hroot : x ^ r⁻¹ = y := by
    dsimp only [x, y]
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hscale₁ : Real.sqrt x * y ^ (1 - r) = s := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [x, y, s]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hscale₂ : s * w = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [s, w, x]
    rw [← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  have hcut := centered_root_tail (r := r) hr.le (zero_lt_one.trans_le hx1)
  dsimp only at hcut
  change centered r x = _ at hcut
  rw [hroot] at hcut
  have h := root_spectral_transform hr v
  dsimp only at h
  change r * s * (-(zeroTail (Real.log y)).re + (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) = _ at h
  have he := (q_weighted_transport hr hv).1
  have hZ := (weighted_zero_tail hr v).1
  have hz : IntegrableOn (fun t => t ^ (-r) * (zeroTail (Real.log t)).re) (Ioi y) := by
    have hRe := hZ.re
    change IntegrableOn (fun t : ℝ => ((t ^ (-r)) • zeroTail (Real.log t)).re) (Ioi y) at hRe
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using hRe
  have hsplit : (∫ t in Ioi y, t ^ (-r) * Q t) =
      (∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re) := by
    rw [← integral_sub (f := fun t => t ^ (-r) * qError t)
      (g := fun t => t ^ (-r) * (zeroTail (Real.log t)).re) he hz]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by unfold qError; ring)
  have hdiff : centered r x - rootDensity r (r * v) =
      r * s * (qError y - (r - 1) * w * (∫ t in Ioi y, t ^ (-r) * qError t)) := by
    rw [hcut, ← h, hsplit]
    change _ = r * s * (Q y + (zeroTail (Real.log y)).re - (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * qError t))
    linear_combination r * Q y * hscale₁ + r * (r - 1) *
      ((∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) * hscale₂
  have hscale : s = Real.exp (-(r * v) / 2) * Real.exp v := by
    dsimp only [s]
    rw [← Real.exp_add]
    congr 1
    ring
  change |centered r x - rootDensity r (r * v)| ≤ _
  rw [hdiff, hscale, show r * (Real.exp (-(r * v) / 2) * Real.exp v) =
    Real.exp (-(r * v) / 2) * (r * Real.exp v) by ring, mul_assoc, abs_mul,
    abs_of_pos (Real.exp_pos _), mul_comm (Real.exp (-(r * v) / 2))]
  exact mul_le_mul_of_nonneg_right (q_weighted_log_bound hn hv) (Real.exp_nonneg _)

private def orderRate (m : ℕ) : ℝ := 1 / 2 - (m + 1 : ℝ)⁻¹

private def capturedSpectrum (m n : ℕ) (u : ℝ) : ℝ :=
  if 2 * n < m + 1 then rootDensity (n : ℝ) u else 0

private theorem centered_after_spectrum_log {Z : ℝ} (hZ₀ : 0 < Z)
    (hZ : ∀ r ≥ 2, ∀ u : ℝ, |rootDensity r u| ≤ Z * (1 + Real.log r)^2 *
      Real.exp (((2 * r)⁻¹ - 1 / 2) * u))
    {m n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    |centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u| ≤
      (trivialConstant + Z) * (1 + Real.log n)^2 * Real.exp (-(orderRate m) * u) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hu' : 0 ≤ u / (n : ℝ) := div_nonneg hu hn0.le
  have hc := root_centered_log_bound hn hu'
  rw [mul_div_cancel₀ _ hn0.ne'] at hc
  have hrate : orderRate m ≤ 1 / 2 := by
    unfold orderRate
    have hp : 0 ≤ ((m + 1 : ℝ))⁻¹ := by positivity
    linarith
  have hexp : Real.exp (-u / 2) ≤ Real.exp (-(orderRate m) * u) := by
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hrate) hu])
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  have hlog_sq : 1 + Real.log n ≤ (1 + Real.log n)^2 := by nlinarith [sq_nonneg (Real.log n)]
  have hcenter : |centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u| ≤
      trivialConstant * (1 + Real.log n)^2 * Real.exp (-(orderRate m) * u) :=
    hc.trans (mul_le_mul (mul_le_mul_of_nonneg_left hlog_sq (by unfold trivialConstant; positivity))
      hexp (Real.exp_nonneg _) (by unfold trivialConstant; positivity))
  unfold capturedSpectrum
  split_ifs with hsmall
  · exact hcenter.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) (Real.exp_nonneg _))
  · have hidx : (m + 1 : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast (le_of_not_gt hsmall)
    have hm₀ : 0 < (m + 1 : ℝ) := by positivity
    have hinv := inv_anti₀ hm₀ hidx
    have hdecay :
        Real.exp (((2 * (n : ℝ))⁻¹ - 1 / 2) * u) ≤ Real.exp (-(orderRate m) * u) := by
      exact Real.exp_le_exp.mpr (by
        unfold orderRate
        nlinarith [mul_nonneg (sub_nonneg.mpr hinv) hu])
    have h := hZ n hn₂ u
    rw [sub_zero, ← sub_add_cancel (centered _ _) (rootDensity _ _)]
    calc
      _ ≤ |centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u| +
          |rootDensity (n : ℝ) u| := abs_add_le _ _
      _ ≤ trivialConstant * (1 + Real.log n)^2 * Real.exp (-(orderRate m) * u) +
          Z * (1 + Real.log n)^2 * Real.exp (-(orderRate m) * u) :=
        add_le_add hcenter (h.trans (mul_le_mul_of_nonneg_left hdecay (by positivity)))
      _ = _ := by ring

private def arithmeticRate (n : ℕ) : ℝ := 1 / 2 - (n : ℝ)⁻¹

private def retainedDensity (m n : ℕ) (u : ℝ) : ℝ :=
  -(μ n : ℝ) * ((n : ℝ) / ((n : ℝ) - 1) *
    Real.exp (-(arithmeticRate n) * u) + capturedSpectrum m n u)

private theorem integrated_mobius_linear {m : ℕ} (hm : 2 ≤ m) {u : ℝ}
    (hx : 2 ≤ Real.exp u) :
    |Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
      ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (Real.sqrt (Real.exp u) *
        (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2))| ≤
      (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2) * (m : ℝ) *
        Real.exp (-(orderRate m) * u) := by
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := (Real.log 4 + 4) * 2
  let p := (m + 1 : ℝ)⁻¹
  have hp₀ : 0 ≤ p := by positivity
  have hp₃ : p ≤ 1 / 3 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hcoef : c * (1 + (m + 1 : ℝ) / Real.log 2) / (1 - p) ≤
      (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2) * (m : ℝ) := by
    have hc : 0 ≤ c * (1 + (m + 1 : ℝ) / Real.log 2) := by positivity
    have hlinear : 1 + (m + 1 : ℝ) / Real.log 2 ≤ (1 + 2 / Real.log 2) * (m : ℝ) := by
      have hdiv := div_le_div_of_nonneg_right (show (m : ℝ) + 1 ≤ 2 * m by linarith) hlog.le
      rw [mul_div_right_comm] at hdiv
      nlinarith [hdiv]
    calc
      _ ≤ c * (1 + (m + 1 : ℝ) / Real.log 2) * 2 := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - p)).mpr
        nlinarith only [mul_nonneg hc (show 0 ≤ 2 * (1 - p) - 1 by linarith)]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ c * 2 by positivity)
        dsimp [c]
        nlinarith only [h]
  have H := integrated_mobius_truncation hm hx
  rw [← Real.exp_mul] at H
  have heq : u * (1 / (m + 1 : ℝ) - 1 / 2) = -(orderRate m) * u := by
    unfold orderRate
    rw [one_div]
    ring
  rw [heq] at H
  rw [mul_sub, Finset.mul_sum] at H
  simp_rw [one_div] at H
  have he :
      Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
        ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (Real.sqrt (Real.exp u) *
          (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2)) =
      Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
        ∑ n ∈ Finset.Icc 2 m, Real.sqrt (Real.exp u) * ((μ n : ℝ) *
          (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2)) := by
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [he]
  exact H.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))

private theorem all_orders_density_log_sq (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * ((m : ℝ) * (1 + Real.log m)^2) * Real.exp (-(orderRate m) * u) := by
  obtain ⟨Z, hZ₀, hZ⟩ := root_density_log_sq hRH
  let A := (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2)
  let L := trivialConstant + Z
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by unfold L trivialConstant; positivity
  have hC : 0 ≤ C := abs_nonneg _
  refine ⟨A + L + C, by linarith, fun m hm u hu => ?_⟩
  let x := Real.exp u
  let W := Real.exp (-(orderRate m) * u)
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t ^ 2)
  let e (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - capturedSpectrum m n u)
  let R := Real.sqrt x * (primeTail x - Q x) - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n
  let E := RHSharpActualEnvelope.G u - Real.exp (-u / 2) * (actualH u).re
  have hx : 2 ≤ x := by
    have hexp : Real.exp (Real.log 2) ≤ Real.exp u := Real.exp_le_exp.mpr hu
    simpa only [x, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ u := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hu
  have hW : 0 < W := Real.exp_pos _
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hR : |R| ≤ A * (m : ℝ) * W := integrated_mobius_linear hm hx
  have hE : |E| ≤ C * W := by
    refine (abs_G_sub_normalized_actualH_le hu0).le.trans ?_
    dsimp only [W]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul (le_abs_self _) _ (Real.exp_nonneg _) hC
    apply Real.exp_le_exp.mpr
    unfold orderRate
    nlinarith [mul_nonneg (show 0 ≤ (m + 1 : ℝ)⁻¹ by positivity) hu0]
  let M := (1 + Real.log m)^2
  have hM : 1 ≤ M := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ m by linarith)
    dsimp [M]
    nlinarith [sq_nonneg (Real.log m)]
  have he (n : ℕ) (hn : n ∈ Finset.Icc 2 m) : |e n| ≤ L * M * W := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hnm : (n : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hlog := Real.log_le_log (zero_lt_one.trans_le hn1) hnm
    have hsq : (1 + Real.log n)^2 ≤ M :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hn1]) (by linarith) _
    have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
    dsimp only [e]
    rw [abs_mul, abs_neg]
    exact (mul_le_of_le_one_left (abs_nonneg _) hμ).trans
      ((centered_after_spectrum_log hZ₀ hZ hn2 hu0).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hL.le) hW.le))
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ L * ((m : ℝ) * M) * W := by
    have hcard : ((Finset.Icc 2 m).card : ℝ) ≤ m := by
      exact_mod_cast (show (Finset.Icc 2 m).card ≤ m by rw [Nat.card_Icc]; omega)
    calc
      _ ≤ ∑ n ∈ Finset.Icc 2 m, |e n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc 2 m, L * M * W := Finset.sum_le_sum he
      _ = ((Finset.Icc 2 m).card : ℝ) * (L * M * W) := by simp
      _ ≤ _ := (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)
  have hterms (n : ℕ) (hn : n ∈ Finset.Icc 2 m) :
      (μ n : ℝ) * T n + retainedDensity m n u + e n = 0 := by
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by have := (Finset.mem_Icc.mp hn).1; omega)
    have ht := root_tail_main (r := (n : ℝ)) hn1 hx0
    change T n = (n : ℝ) / ((n : ℝ) - 1) * x ^ ((n : ℝ)⁻¹ - 1 / 2) + centered (n : ℝ) x at ht
    have hpow : x ^ ((n : ℝ)⁻¹ - 1 / 2) = Real.exp (-(arithmeticRate n) * u) := by
      dsimp only [x, arithmeticRate]
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [ht, hpow]
    unfold retainedDensity e
    ring
  have hs : (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n) +
      (∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) +
      (∑ n ∈ Finset.Icc 2 m, e n) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl hterms).trans Finset.sum_const_zero
  have hsplit : rootWindowDensity u - ∑ n ∈ Finset.Icc 2 m, retainedDensity m n u =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E - 2 := by
    dsimp only [R, E, rootWindowDensity, x]
    linear_combination -hs
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E by linarith only [hsplit]]
  have hm₁ : (1 : ℝ) ≤ m := by linarith
  have hms : (m : ℝ) ≤ (m : ℝ) * M := by
    simpa using mul_le_mul_of_nonneg_left hM (show 0 ≤ (m : ℝ) by positivity)
  have hms₁ : (1 : ℝ) ≤ (m : ℝ) * M := hm₁.trans hms
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      calc
        _ ≤ |-R + ∑ n ∈ Finset.Icc 2 m, e n| + |E| := abs_add_le _ _
        _ ≤ (|-R| + |∑ n ∈ Finset.Icc 2 m, e n|) + |E| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_neg]
    _ ≤ A * ((m : ℝ) * (1 + Real.log m)^2) * W + L * ((m : ℝ) * (1 + Real.log m)^2) * W + C * ((m : ℝ) * (1 + Real.log m)^2) * W :=
      add_le_add (add_le_add (hR.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hms hA.le) hW.le)) hsum)
        (hE.trans (mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hms₁ hC) hW.le))
    _ = _ := by ring

private def powerGap (s a B : ℝ) : ℝ := a ^ (-s) - B ^ (-s)

private def arithmeticPrimitive (n : ℕ) (a B : ℝ) : ℝ :=
  -(μ n : ℝ) * (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
    powerGap (arithmeticRate n) a B

private def capturedPrimitive (m n : ℕ) (a B : ℝ) : ℝ :=
  if 2 * n < m + 1 then -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a) else 0

private theorem root_rate_positive {n : ℕ} (hn : 3 ≤ n) : 0 < arithmeticRate n := by
  have hn₀ : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hi := inv_strictAnti₀ (show (0 : ℝ) < 2 by norm_num) hn₀
  exact sub_pos.mpr (by simpa only [one_div] using hi)

private theorem retainedDensity_integral {m n : ℕ} (hn : 2 ≤ n) {a B : ℝ}
    (ha : 0 < a) (hB : 0 < B) :
    IntervalIntegrable (retainedDensity m n) volume (Real.log a) (Real.log B) ∧
      (∫ u in Real.log a..Real.log B, retainedDensity m n u) =
        (if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) +
          capturedPrimitive m n a B := by
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hi : IntervalIntegrable (fun u : ℝ => (n : ℝ) / ((n : ℝ) - 1) *
      Real.exp (-(arithmeticRate n) * u)) volume (Real.log a) (Real.log B) :=
    (by fun_prop : Continuous (fun u : ℝ => (n : ℝ) / ((n : ℝ) - 1) *
      Real.exp (-(arithmeticRate n) * u))).intervalIntegrable _ _
  have hs : IntervalIntegrable (capturedSpectrum m n) volume (Real.log a) (Real.log B) ∧
      -(μ n : ℝ) * (∫ u in Real.log a..Real.log B, capturedSpectrum m n u) =
        capturedPrimitive m n a B := by
    by_cases h : 2 * n < m + 1
    · have heq : capturedSpectrum m n = rootDensity (n : ℝ) := by
        funext u
        simp [capturedSpectrum, h]
      obtain ⟨hi', he⟩ := root_density_integral hn₁ (Real.log a) (Real.log B)
      rw [heq, he, Real.exp_log hB, Real.exp_log ha, capturedPrimitive, ite_eq_left h]
      exact ⟨hi', rfl⟩
    · have heq : capturedSpectrum m n = fun _ => 0 := by
        funext u
        simp [capturedSpectrum, h]
      rw [heq, capturedPrimitive, ite_eq_right h]
      exact ⟨intervalIntegrable_const, by simp⟩
  refine ⟨(hi.add hs.1).const_mul _, ?_⟩
  unfold retainedDensity
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi hs.1, mul_add, hs.2]
  congr 1
  by_cases he : n = 2
  · subst n
    have hμ : μ 2 = -1 := moebius_apply_prime Nat.prime_two
    simp [arithmeticRate, hμ, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · rw [ite_eq_right he, intervalIntegral.integral_const_mul, exp_decay_integral (root_rate_positive (by omega))]
    have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
      rw [Real.rpow_def_of_pos hx, mul_comm]
    rw [hrpow ha, hrpow hB]
    unfold arithmeticPrimitive powerGap
    have hn₂ : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
    have hn₀ : (0 : ℝ) < n := zero_lt_two.trans hn₂
    have hrate : arithmeticRate n = ((n : ℝ) - 2) / (2 * (n : ℝ)) := by
      unfold arithmeticRate
      field_simp
    rw [hrate]
    have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
    field_simp

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)

/-- Under RH, one pair of constants bounds the prime-window residual at every truncation degree. -/
theorem prime_window_mobius_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * ((m : ℝ) * (1 + Real.log m)^2) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (late_strict_prime_tail hRH)
  obtain ⟨K, hK, hD⟩ := all_orders_density_log_sq hRH
  refine ⟨max T 2, 6 * K, le_max_right _ _, by positivity, ?_⟩
  intro m hm a B ha hab
  have h_arithmetic (n : ℕ) : -(arithmeticRate n) = (n : ℝ)⁻¹ - 1 / 2 := by
    unfold arithmeticRate
    ring
  have h_order : -(orderRate m) = (m + 1 : ℝ)⁻¹ - 1 / 2 := by
    unfold orderRate
    ring
  simp_rw [← h_order, ← h_arithmetic]
  change |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a)) -
      (∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B) -
      (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
        -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
      6 * K * ((m : ℝ) * (1 + Real.log m)^2) * powerGap (orderRate m) a B
  have ha₂ := (le_max_right T (2 : ℝ)).trans ha
  have ha₀ : 0 < a := by linarith
  have hB₀ := ha₀.trans_le hab
  have hlog := Real.log_le_log ha₀ hab
  have hlog₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha₂
  have hr : 1 / 6 ≤ orderRate m := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h := inv_anti₀ (show (0 : ℝ) < 3 by norm_num)
      (show (3 : ℝ) ≤ (m + 1 : ℝ) by linarith)
    unfold orderRate
    norm_num at h
    linarith
  have hr₀ : 0 < orderRate m := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hr
  have Hwin : (∫ u in Real.log a..Real.log B, windowError u) =
      ∫ u in Real.log a..Real.log B, rootWindowDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hlog] at hu
    have hx : a ≤ Real.exp u := by simpa only [Real.exp_log ha₀] using Real.exp_le_exp.mpr hu.1
    have hpos := hT _ ((le_max_left T 2).trans (ha.trans hx))
    have hscaled := complete_scaled (x := Real.exp u) (ha₂.trans hx)
    rw [Real.log_exp] at hscaled
    rw [windowError, normalizedMass, normalizedZeroSeries, max_eq_left hpos.le,
      rootWindowDensity, Complex.re_ofReal_mul, hscaled]
    ring
  let f (u : ℝ) := ∑ n ∈ Finset.Icc 2 m, retainedDensity m n u
  let e (u : ℝ) := rootWindowDensity u - (f u - 2)
  let w (u : ℝ) := K * ((m : ℝ) * (1 + Real.log m)^2) * Real.exp (-(orderRate m) * u)
  have hi : IntervalIntegrable rootWindowDensity volume (Real.log a) (Real.log B) :=
    (rootWindowDensity_continuousOn.mono (by
      rw [uIcc_of_le hlog]
      exact fun _ hu => hlog₂.trans hu.1)).intervalIntegrable
  have hfi : IntervalIntegrable f volume (Real.log a) (Real.log B) := by
    have hf : f = ∑ n ∈ Finset.Icc 2 m, retainedDensity m n := by
      funext u
      simp [f, Finset.sum_apply]
    rw [hf]
    exact IntervalIntegrable.sum (f := retainedDensity m) (Finset.Icc 2 m) (fun n hn =>
      (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1)
  have hc : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume (Real.log a) (Real.log B) :=
    intervalIntegrable_const
  have hei : IntervalIntegrable e volume (Real.log a) (Real.log B) := hi.sub (hfi.sub hc)
  have hwi : IntervalIntegrable w volume (Real.log a) (Real.log B) :=
    (by unfold w; fun_prop : Continuous w).intervalIntegrable _ _
  have hmono : |∫ u in Real.log a..Real.log B, e u| ≤ ∫ u in Real.log a..Real.log B, w u :=
    (intervalIntegral.abs_integral_le_integral_abs hlog).trans
      (intervalIntegral.integral_mono_on hlog hei.abs hwi (fun u hu => hD m hm u (hlog₂.trans hu.1)))
  have Hf : (∫ u in Real.log a..Real.log B, f u) =
      2 * (Real.log B - Real.log a) +
        (∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B) +
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a)) := by
    unfold f
    rw [intervalIntegral.integral_finsetSum fun n hn =>
      (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1]
    calc
      _ = ∑ n ∈ Finset.Icc 2 m,
          ((if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) +
            capturedPrimitive m n a B) :=
        Finset.sum_congr rfl fun _ hn => (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).2
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have hs : Finset.Icc 2 m = insert 2 (Finset.Icc 3 m) := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hmain :
            (∑ n ∈ Finset.Icc 2 m,
              if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) =
              2 * (Real.log B - Real.log a) + ∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B := by
          rw [hs, Finset.sum_insert (by simp)]
          congr 1
          exact Finset.sum_congr rfl fun n hn => ite_eq_right (by have := (Finset.mem_Icc.mp hn).1; omega)
        rw [hmain, Finset.sum_filter]
        rfl
  have hw : (∫ u in Real.log a..Real.log B, w u) =
      K * ((m : ℝ) * (1 + Real.log m)^2) * (powerGap (orderRate m) a B / orderRate m) := by
    unfold w
    rw [intervalIntegral.integral_const_mul, exp_decay_integral hr₀]
    have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
      rw [Real.rpow_def_of_pos hx, mul_comm]
    rw [hrpow ha₀, hrpow hB₀]
    rfl
  have hgap : 0 ≤ powerGap (orderRate m) a B :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos ha₀ hab (neg_nonpos.mpr hr₀.le))
  have hdiv : powerGap (orderRate m) a B / orderRate m ≤ 6 * powerGap (orderRate m) a B := by
    apply (div_le_iff₀ hr₀).mpr
    nlinarith only [mul_nonneg hgap (show 0 ≤ 6 * orderRate m - 1 by linarith)]
  rw [(prime_window_remainder_of_rh hRH).2.2 a B ha₂ hab, Hwin]
  have hle : (∫ u in Real.log a..Real.log B, w u) ≤
      6 * K * ((m : ℝ) * (1 + Real.log m)^2) * powerGap (orderRate m) a B := by
    rw [hw]
    exact (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans_eq (by ring)
  refine (?_ : _ ≤ ∫ u in Real.log a..Real.log B, w u).trans hle
  dsimp only [e] at hmono
  rw [intervalIntegral.integral_sub hi (hfi.sub hc), intervalIntegral.integral_sub hfi hc, Hf,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  convert hmono using 1
  congr 1
  ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
