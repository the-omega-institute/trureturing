/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourier
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier recovery of actual zero frequencies and analytic multiplicities from even-cutoff signed prime windows. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoff
import Mathlib.NumberTheory.LSeries.ZetaZeros

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open MeasureTheory

open Set
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)

/-- Each tested frequency is separated from the remaining distinct modes of the actual zeros. -/
private theorem actual_frequency_gap {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, frequency k / (r : ℂ) ≠ w →
      δ ≤ ‖frequency k / (r : ℂ)-w‖ := by
  let center : ℂ := 1/2 + (r : ℂ)*w
  let otherZeros := riemannZetaZeros \ {center}
  have hclosed : IsClosed otherZeros :=
    isClosed_of_subset_discrete_closed Set.sdiff_subset isDiscrete_riemannZetaZeros
      isClosed_riemannZetaZeros
  have hcenter : center ∈ otherZerosᶜ := by simp [otherZeros]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl center hcenter
  refine ⟨ε/r, div_pos hε hr, fun k hk => ?_⟩
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hspace : frequency k / (r : ℂ) - w = (actualZero k - center)/(r : ℂ) := by
    dsimp only [frequency, center]
    field_simp
    ring
  have hz : actualZero k ∈ riemannZetaZeros :=
    (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).1
  have hne : actualZero k ≠ center := by
    intro h
    apply hk
    apply sub_eq_zero.mp
    rw [hspace, h, sub_self, zero_div]
  have hsep : ε ≤ ‖actualZero k - center‖ := by
    by_contra! hlt
    have hmem : actualZero k ∈ Metric.ball center ε := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hlt
    exact (hball hmem) ⟨hz, fun h => hne (Set.mem_singleton_iff.mp h)⟩
  rw [hspace, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact div_le_div_of_nonneg_right hsep hr.le

open scoped ComplexConjugate
open D5.S3.Weil.Mertens.IntegratedExplicit (actual_complete_H_package)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private theorem normalized_width_series_real (r L u : ℝ) :
    let s := 1/2-(2*r)⁻¹
    let mode := fun k : ℕ => frequency k/(r : ℂ)
    let coeff := fun k : ℕ => rootCoeff r k / rootExponent r k *
      ((Complex.exp (((-(s : ℂ)) + mode k)*(L : ℂ))-1)/((1-Real.exp (-s*L) : ℝ) : ℂ))
    let z := ∑' k, coeff k * Complex.exp (mode k*(u : ℂ))
    (z.re : ℂ) = z := by
  let s : ℝ := 1/2-(2*r)⁻¹
  let mode (k : ℕ) := frequency k/(r : ℂ)
  let coeff (k : ℕ) := rootCoeff r k / rootExponent r k *
      ((Complex.exp (((-(s : ℂ)) + mode k)*(L : ℂ))-1)/((1-Real.exp (-s*L) : ℝ) : ℂ))
  let f (k : ℕ) := coeff k * Complex.exp (mode k*(u : ℂ))
  obtain ⟨_, p, hp, _⟩ := actual_complete_H_package
  have hc (k : ℕ) : conj (f k) = f (p k) := by
    simp [f, coeff, rootCoeff, rootExponent, mode, frequency, hp, ← Complex.exp_conj, map_ofNat]
  have he : conj (∑' k, f k) = ∑' k, f k := by
    rw [Complex.conj_tsum]
    simp_rw [hc]
    exact p.tsum_eq f
  have him := congrArg Complex.im he
  simp only [Complex.conj_im] at him
  have hzero : (∑' k, f k).im = 0 := by linarith
  change (((∑' k, f k).re : ℝ) : ℂ) = _
  apply Complex.ext
  · exact Complex.ofReal_re _
  · rw [Complex.ofReal_im, hzero]

open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency_real frequency_norm)
open D5.S3.Weil.Mertens.IntegratedExplicit (occurrence_hasSum)

private theorem actual_frequency_multiplicity {r : ℝ} (hr : 0 < r)
    (n : ℕ) (a : ℂ → ℂ) :
    (∑' k : ℕ, if frequency k/(r : ℂ) = (actualData.zero n - 1/2)/(r : ℂ)
      then a (actualZero k) else 0) =
      (actualData.multiplicity n : ℂ)*a (actualData.zero n) := by
  let f (z : ℂ) := if z = actualData.zero n then a z else 0
  have hsig (j : ℕ) : actualData.multiplicity j • f (actualData.zero j) =
      if j = n then (actualData.multiplicity n : ℂ)*a (actualData.zero n) else 0 := by
    by_cases h : j = n
    · subst j
      simp [f, nsmul_eq_mul]
    · simp [f, h, show actualData.zero j ≠ actualData.zero n from fun hz => h (actualData.zero_injective hz)]
  have hs : HasSum (fun j => (actualData.multiplicity j : ℂ) * f (actualData.zero j))
      ((actualData.multiplicity n : ℂ)*a (actualData.zero n)) := by
    convert hasSum_ite_eq n ((actualData.multiplicity n : ℂ)*a (actualData.zero n)) using 1
    funext j
    simpa only [nsmul_eq_mul] using hsig j
  have hf := (occurrence_hasSum hs).tsum_eq
  convert hf using 1
  apply tsum_congr
  intro k
  have hnonzero : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : (frequency k / (r : ℂ) = (actualData.zero n - 1/2) / (r : ℂ)) ↔
      actualZero k = actualData.zero n := by
    rw [div_left_inj' hnonzero]
    simp [frequency]
  simp only [f, he]

open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)

/-- The complex frequency of a zero after rescaling by the root degree. -/
noncomputable def windowMode (r : ℝ) (z : ℂ) : ℂ := (z-1/2)/(r : ℂ)

/-- The contribution of one occurrence to the normalized root increment at width L. -/
noncomputable def windowCoefficient (r L : ℝ) (z : ℂ) : ℂ :=
  let s : ℝ := 1/2-(2*r)⁻¹
  (2*(r : ℂ)^2)/(z*((r : ℂ)-z)*((r : ℂ)-2*z)) *
    ((Complex.exp (((-(s : ℂ)) + windowMode r z)*(L : ℂ))-1)/((1-Real.exp (-s*L) : ℝ) : ℂ))

theorem window_coefficient_of_occurrence {r : ℝ} (hr : 1 < r) (L : ℝ) (k : ℕ) :
    let s : ℝ := 1/2-(2*r)⁻¹
    windowCoefficient r L (actualZero k) = rootCoeff r k / rootExponent r k *
      ((Complex.exp (((-(s : ℂ)) + frequency k/(r : ℂ))*(L : ℂ))-1)/
        ((1-Real.exp (-s*L) : ℝ) : ℂ)) := by
  have h := rootPrimitiveMode_eq hr 0 k
  simp [rootMode, Real.exp_zero] at h
  simp only [windowCoefficient, windowMode, frequency]
  rw [h]

/-- The normalized fixed-width primitive has absolutely summable coefficients. -/
theorem window_coefficients_summable (hRH : RiemannHypothesis) {r L : ℝ}
    (hr : 1 < r) (hL : 0 < L) :
    Summable (fun k => ‖windowCoefficient r L (actualZero k)‖) := by
  let s : ℝ := 1/2-(2*r)⁻¹
  let t := Real.exp (-s*L)
  have hs : 0 < s := by
    dsimp only [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (show 2 < 2*r by linarith))
  have hd : 0 < 1-t := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL))
  let C := (t+1)/(1-t)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  apply (((actualCoeff_hasSum.summable.norm.mul_left r).mul_right r).mul_right C).of_nonneg_of_le
  · exact fun _ => norm_nonneg _
  · intro k
    rw [window_coefficient_of_occurrence hr L k]
    set v := frequency k/(r : ℂ) with hv
    have hmode : v.re = 0 := by simp [hv, Complex.div_re, frequency_real hRH k]
    have hexp : ‖Complex.exp ((-(s : ℂ)+v)*(L : ℂ))‖ = t := by
      simp [Complex.norm_exp, Complex.mul_re, Complex.add_re, hmode, t]
    rw [norm_mul]
    refine mul_le_mul (root_primitive_coefficient_norm_le hr k) ?_ (norm_nonneg _) (by positivity)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    exact div_le_div_of_nonneg_right
      (by simpa only [hexp, norm_one] using norm_sub_le (Complex.exp ((-(s : ℂ)+v)*(L : ℂ))) 1) hd.le


/-- The normalized root increment equals its full fixed-width centered series. -/
theorem normalized_width_series (hRH : RiemannHypothesis) {r L : ℝ}
    (hr : 1 < r) (hL : 0 < L) (u : ℝ) :
    let s : ℝ := 1/2-(2*r)⁻¹
    (((rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
        powerGap s (Real.exp u) (Real.exp (u+L)) : ℝ) : ℂ) =
      ∑' k, windowCoefficient r L (actualZero k) *
        Complex.exp ((frequency k/(r : ℂ))*(u : ℂ)) := by
  let s : ℝ := 1/2-(2*r)⁻¹
  let t := Real.exp (-s*L)
  let a (k : ℕ) := rootCoeff r k / rootExponent r k
  let v (k : ℕ) := frequency k / (r : ℂ)
  let z (y : ℝ) := ∑' k, a k * Complex.exp (v k*(y : ℂ))
  have hs : 0 < s := by
    dsimp only [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (show 2 < 2*r by linarith))
  have hd : 0 < 1-t := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL))
  have hcoeff : Summable (fun k => ‖a k‖) := by
    apply ((actualCoeff_hasSum.summable.norm.mul_left r).mul_right r).of_nonneg_of_le
    · exact fun _ => norm_nonneg _
    · exact root_primitive_coefficient_norm_le hr
  have hv (k : ℕ) : (v k).re = 0 := by simp [v, Complex.div_re, frequency_real hRH k]
  have ht (y : ℝ) : Summable (fun k => a k * Complex.exp (v k*(y : ℂ))) := by
    apply hcoeff.of_norm_bounded
    intro k
    simp [Complex.norm_exp, Complex.mul_re, hv k]
  have hden (y : ℝ) : Real.exp (-s*y) = (Real.exp (s*y))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hshift : t * Real.exp (s*(u+L)) = Real.exp (s*u) := by
    dsimp only [t]
    rw [← Real.exp_add]
    congr 1
    ring
  have heq :
      (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
          powerGap s (Real.exp u) (Real.exp (u+L)) =
        (t*(z (u+L)).re-(z u).re)/(1-t) := by
    have hh (y : ℝ) : Real.exp (s*y)*rootPrimitive r (Real.exp y) = (z y).re :=
      normalized_root_primitive_series hr y
    rw [← hh, ← hh, ← mul_assoc, hshift, ← mul_sub, exp_power_gap, hden]
    change _ / ((Real.exp (s*u))⁻¹*(1-t)) = _
    field_simp [(Real.exp_pos (s*u)).ne', hd.ne']
  have hseries : ((t : ℂ)*z (u+L)-z u)/((1-t : ℝ) : ℂ) =
      ∑' k, windowCoefficient r L (actualZero k)*Complex.exp (v k*(u : ℂ)) := by
    dsimp only [z]
    rw [← tsum_mul_left, ← ((ht (u+L)).mul_left (t : ℂ)).tsum_sub (ht u), ← tsum_div_const]
    apply tsum_congr
    intro k
    rw [window_coefficient_of_occurrence hr L k]
    change ((t : ℂ) * (a k*Complex.exp (v k*((u+L : ℝ) : ℂ))) -
        a k*Complex.exp (v k*(u : ℂ)))/((1-t : ℝ) : ℂ) =
      (a k*((Complex.exp ((-(s : ℂ)+v k)*(L : ℂ))-1)/((1-t : ℝ) : ℂ))) *
        Complex.exp (v k*(u : ℂ))
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    have htranslate : (t : ℂ)*Complex.exp (v k*(L : ℂ)) =
        Complex.exp ((-(s : ℂ)+v k)*(L : ℂ)) := by
      dsimp only [t]
      rw [Complex.ofReal_exp]
      push_cast
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [show (t : ℂ) * (a k*(Complex.exp (v k*(u : ℂ))*Complex.exp (v k*(L : ℂ)))) =
      a k * Complex.exp (v k*(u : ℂ)) * ((t : ℂ)*Complex.exp (v k*(L : ℂ))) by ring,
      htranslate]
    ring
  have hreal :
      (((∑' k, windowCoefficient r L (actualZero k)*Complex.exp (v k*(u : ℂ))).re : ℝ) : ℂ) =
        ∑' k, windowCoefficient r L (actualZero k)*Complex.exp (v k*(u : ℂ)) := by
    simp_rw [window_coefficient_of_occurrence hr L]
    exact normalized_width_series_real r L u
  change ((_:ℝ) : ℂ) = _
  rw [heq, ← hreal, ← hseries]
  congr 1
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.re_ofReal_mul]

private theorem integral_character_sub_constant (a w : ℂ) (hw : w.re = 0)
    (U T : ℝ) :
    ‖(∫ u in U..U+T, a * Complex.exp (-w*(u : ℂ))) -
        (T : ℂ)*(if w=0 then a else 0)‖ ≤ ‖a‖ * (2/‖w‖) := by
  by_cases hz : w = 0
  · subst w
    simp [intervalIntegral.integral_const, Complex.real_smul, add_sub_cancel_left, mul_comm]
  · have hh : (-w).re = 0 := by simp [hw]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hz
    have h := bounded_exponential_integral hh hwpos (by rw [norm_neg]) U (U+T)
    rw [ite_eq_right hz, mul_zero, sub_zero, intervalIntegral.integral_const_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

private theorem window_coefficient_nonzero (hRH : RiemannHypothesis) {r L : ℝ}
    (hr : 1 < r) (hL : 0 < L) {z : ℂ} (hz : IsNontrivialZero z) :
    windowCoefficient r L z ≠ 0 := by
  let s : ℝ := 1/2-(2*r)⁻¹
  have hs : 0 < s := by
    dsimp only [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (show 2 < 2*r by linarith))
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hz
  let k := actualOccurrenceEquiv.symm ⟨n, ⟨0, actualData.multiplicity_pos n⟩⟩
  have hk : actualZero k = z := by simp [actualZero, k, hn]
  have hre : z.re = 1/2 := by
    have h := frequency_real hRH k
    simpa [frequency, hk, sub_eq_zero] using h
  have hv : (windowMode r z).re = 0 := by
    simp [windowMode, Complex.div_re, Complex.sub_re, hre]
  have hden := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL))
  have hexp : Complex.exp ((-(s : ℂ)+windowMode r z)*(L : ℂ)) ≠ 1 := by
    apply ne_of_apply_ne norm
    have hn : ‖Complex.exp ((-(s : ℂ)+windowMode r z)*(L : ℂ))‖ = Real.exp (-s*L) := by
      simp [Complex.norm_exp, Complex.mul_re, Complex.add_re, hv]
    rw [hn, norm_one]
    exact (sub_pos.mp hden).ne
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre; norm_num at hre
  have hzr : (r : ℂ)-z ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp [hre] at he
    linarith
  have hzr' : (r : ℂ)-2*z ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp [Complex.mul_re, hre] at he
    linarith
  unfold windowCoefficient
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hr0))
    (mul_ne_zero (mul_ne_zero hz0 hzr) hzr'))
    (div_ne_zero (sub_ne_zero.mpr hexp) (Complex.ofReal_ne_zero.mpr hden.ne'))

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The coefficient mass controls the width dependence of the Fourier error. -/
theorem signed_window_even_cutoff_fourier_bound (hRH : RiemannHypothesis) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ m r : ℕ, 2 ≤ m → m+1 = 2*r →
      ∀ ω : ℝ, ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
        ∀ L : ℝ, 0 < L →
        ∀ U T : ℝ, U₀ ≤ U → 0 < T →
          let s := orderRate m
          let w := (ω : ℂ)*Complex.I
          let F := fun u : ℝ => ((signedWindowResidual m (Real.exp u) (Real.exp (u+L)) /
            powerGap s (Real.exp u) (Real.exp (u+L)) : ℝ) : ℂ) * Complex.exp (-w*(u : ℂ))
          let c := (μ (m+1) : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))
          let target := (if ω=0 then -(c : ℂ) else 0) - (μ r : ℂ) *
            (∑' k, if windowMode (r : ℝ) (actualZero k) = w
              then windowCoefficient (r : ℝ) L (actualZero k) else 0)
          IntervalIntegrable F volume U (U+T) ∧
          ‖(∫ u in U..U+T, F u)/(T : ℂ)-target‖ ≤
            (A+B*(∑' k, ‖windowCoefficient (r : ℝ) L (actualZero k)‖))/T := by
  obtain ⟨a₀, K, ha₂, hK, hexpansion⟩ := signed_window_even_cutoff_expansion hRH
  let U₀ := Real.log a₀
  have ha₀ : 0 < a₀ := by linarith
  have hlog : Real.log 2 ≤ U₀ := Real.log_le_log (by norm_num) ha₂
  have hU₀ : 0 < U₀ := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hlog
  refine ⟨U₀, hU₀, fun m r hm heven ω => ?_⟩
  let q := m+1
  let s := orderRate m
  let δ := ((m : ℝ)+1)⁻¹-((m : ℝ)+2)⁻¹
  let c := (μ q : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))
  let W := K*((q : ℝ)*(1+Real.log (q : ℝ))^2)*((s+δ)/s)
  let w := (ω : ℂ)*Complex.I
  let d := (μ r : ℂ)
  let A := if w=0 then -(c : ℂ) else 0
  have hw : w.re = 0 := by simp [w, Complex.mul_re]
  have hr : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hqR : (m : ℝ)+1 = 2*(r : ℝ) := by exact_mod_cast heven
  have hs' : s = 1/2-(2*(r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [hqR]
  have hs : 0 < s := by
    rw [hs', show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (by linarith))
  have hδ : 0 < δ := sub_pos.mpr (inv_strictAnti₀ (by positivity) (by linarith))
  have hW : 0 < W := by dsimp only [W]; positivity
  let mode (k : ℕ) := frequency k/((r : ℝ) : ℂ)
  have hmode (k : ℕ) : (mode k).re = 0 := by
    simp [mode, Complex.div_re, frequency_real hRH k]
  obtain ⟨g, hg, hgap⟩ := actual_frequency_gap (by linarith : 0 < (r : ℝ)) w
  let C₁ := W/δ
  let C₂ := ‖(c : ℂ)‖*(2/‖w‖)
  let M := ‖d‖*(2/g)
  refine ⟨C₁+C₂, M, by dsimp only [C₁, C₂]; positivity, by dsimp only [M]; positivity,
    fun L hL U T hU hT => ?_⟩
  let gap (u : ℝ) := powerGap s (Real.exp u) (Real.exp (u+L))
  let f (u : ℝ) := signedWindowResidual m (Real.exp u) (Real.exp (u+L))/gap u
  let P (u : ℝ) := (rootPrimitive (r : ℝ) (Real.exp (u+L)) -
    rootPrimitive (r : ℝ) (Real.exp u))/gap u
  let R (u : ℝ) := f u+c+(μ r : ℝ)*P u
  let phase (u : ℝ) := Complex.exp (-w*(u : ℂ))
  let coeff (k : ℕ) := windowCoefficient (r : ℝ) L (actualZero k)
  let B := ∑' k, if mode k = w then coeff k else 0
  have hphase (u : ℝ) : ‖phase u‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, hw]
  have hP (u : ℝ) : ((P u : ℝ) : ℂ) = ∑' k, coeff k*Complex.exp (mode k*(u : ℂ)) := by
    simpa only [P, gap, hs', coeff, mode] using normalized_width_series hRH hr hL u
  have hcoeff := window_coefficients_summable hRH hr hL
  let C₃ := (∑' k, ‖coeff k‖)*(2/g)
  let C := (C₁+C₂) + M*(∑' k, ‖coeff k‖)
  let last := U+T
  let E (u : ℝ) := (R u : ℂ)*phase u
  let G (u : ℝ) := -(c : ℂ)*phase u
  let H (u : ℝ) := (P u : ℂ)*phase u
  have hUL : U ≤ last := by dsimp only [last]; linarith
  have hR (u : ℝ) (hu : U₀ ≤ u) : ‖E u‖ ≤ W*Real.exp (-δ*u) := by
    have ha : a₀ ≤ Real.exp u := by
      rw [← Real.exp_log ha₀]
      exact Real.exp_le_exp.mpr hu
    have hab : Real.exp u < Real.exp (u+L) := Real.exp_lt_exp.mpr (by linarith)
    have hd : 0 < gap u :=
      sub_pos.mpr (Real.rpow_lt_rpow_of_neg (Real.exp_pos _) hab (neg_neg_of_pos hs))
    have he := hexpansion m r hm heven (Real.exp u) (Real.exp (u+L)) ha hab.le
    rw [show ‖E u‖ = |R u| by simp [E, hphase, Complex.norm_real, Real.norm_eq_abs]]
    have heR : R u = (signedWindowResidual m (Real.exp u) (Real.exp (u+L)) +
      c*gap u+(μ r : ℝ)*(rootPrimitive (r : ℝ) (Real.exp (u+L)) -
        rootPrimitive (r : ℝ) (Real.exp u)))/gap u := by
      unfold R f P
      field_simp [hd.ne']
    rw [heR, abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    rw [show Real.exp (-δ*u) = (Real.exp u)^(-δ) by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]]
    exact he.1.trans he.2
  have hbound : IntervalIntegrable (fun u => W*Real.exp (-δ*u)) volume U last :=
    (by fun_prop : Continuous fun u : ℝ => W*Real.exp (-δ*u)).intervalIntegrable _ _
  have hPmeas : Measurable (fun u : ℝ => (P u : ℂ)) := by
    simp_rw [hP]
    apply Measurable.tsum
    intro k
    fun_prop
  have hE : IntervalIntegrable E volume U last := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hUL]
    have hbase := (intervalIntegrable_iff_integrableOn_Ioc_of_le hUL).mp hbound
    have hf := window_normalized_aestronglyMeasurable (hlog.trans hU) hUL hL.le m (s := s)
    have hc : AEStronglyMeasurable (fun u : ℝ => (f u : ℂ)) (volume.restrict (Set.Ioc U last)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hf
    have hmP : AEStronglyMeasurable (fun u : ℝ => d*(P u : ℂ)) (volume.restrict (Set.Ioc U last)) :=
      (hPmeas.const_mul d).aestronglyMeasurable
    have hconst : AEStronglyMeasurable (fun _ : ℝ => (c : ℂ)) (volume.restrict (Set.Ioc U last)) :=
      aestronglyMeasurable_const
    have hRMeas := (hc.add hconst).add hmP
    refine hbase.mono' ?_ ?_
    · have hψ : Measurable phase := by unfold phase; fun_prop
      convert hRMeas.mul hψ.aestronglyMeasurable using 1
      funext u
      simp [E, R, d]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hR u (hU.trans hu.1.le)
  have hIE : ‖∫ u in U..last, E u‖ ≤ C₁ := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hUL
      (ae_of_all _ fun u hu => hR u (hU.trans hu.1.le)) hbound).trans ?_
    rw [intervalIntegral.integral_const_mul, exp_decay_integral hδ]
    have hUpos : 0 ≤ U := hU₀.le.trans hU
    have hexp_le : Real.exp (-δ*U) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) hUpos)
    dsimp only [C₁]
    rw [div_eq_mul_inv W δ]
    exact mul_le_mul_of_nonneg_left (by
      rw [← one_div]
      exact div_le_div_of_nonneg_right ((sub_le_self _ (Real.exp_nonneg _)).trans hexp_le) hδ.le) hW.le
  have hG : IntervalIntegrable G volume U last :=
    (by unfold G phase; fun_prop : Continuous G).intervalIntegrable _ _
  have hIG : ‖(∫ u in U..last, G u) - (T : ℂ)*A‖ ≤ C₂ := by
    simpa only [G, phase, A, C₂, norm_neg, last] using
      integral_character_sub_constant (-(c : ℂ)) w hw U T
  obtain ⟨hH', hIH'⟩ := spectral_fiber_average coeff mode hcoeff hmode hw hg hgap U hT
  have heqH : H = fun u : ℝ => (∑' k, coeff k*Complex.exp (mode k*(u : ℂ)))*phase u := by
    funext u
    simp only [H, hP]
  have hH : IntervalIntegrable H volume U last := by simpa only [heqH, phase, last] using hH'
  have hIH : ‖(∫ u in U..last, H u)-(T : ℂ)*B‖ ≤ C₃ := by
    have h' : ‖(∫ u in U..last, H u)/(T : ℂ)-B‖ ≤ C₃/T := by
      simpa only [heqH, phase, B, C₃, last] using hIH'
    have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
    rw [show (∫ u in U..last, H u)/(T : ℂ)-B = ((∫ u in U..last, H u)-(T : ℂ)*B)/(T : ℂ) by
      field_simp [hT0], norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT] at h'
    exact (div_le_div_iff_of_pos_right hT).mp h'
  have heqF : (fun u : ℝ => (f u : ℂ)*phase u) = fun u => E u+G u-d*H u := by
    funext u
    simp only [E, G, H, R, d, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  have hw0 : w = 0 ↔ ω=0 := by simp [w, mul_eq_zero, Complex.I_ne_zero]
  change IntervalIntegrable (fun u => (f u : ℂ)*phase u) volume U last ∧
    ‖(∫ u in U..last, (f u : ℂ)*phase u)/(T : ℂ) -
      ((if ω=0 then -(c : ℂ) else 0)-d*B)‖ ≤ C/T
  have hA : (if ω=0 then -(c : ℂ) else 0) = A := by simp [A, hw0]
  rw [hA, heqF]
  refine ⟨(hE.add hG).sub (hH.const_mul d), ?_⟩
  have hdH : (∫ u in U..last, d*H u) = d*(∫ u in U..last, H u) :=
    intervalIntegral.integral_const_mul d H
  rw [intervalIntegral.integral_sub (hE.add hG) (hH.const_mul d),
    intervalIntegral.integral_add hE hG, hdH]
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  rw [show ((∫ u in U..last, E u)+(∫ u in U..last, G u)-d*(∫ u in U..last, H u))/(T : ℂ)-(A-d*B) =
    ((∫ u in U..last, E u)+((∫ u in U..last, G u)-(T : ℂ)*A)-
      d*((∫ u in U..last, H u)-(T : ℂ)*B))/(T : ℂ) by
      field_simp [hT0]
      ring,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  apply div_le_div_of_nonneg_right _ hT.le
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have he := (norm_add_le (∫ u in U..last, E u) ((∫ u in U..last, G u)-(T : ℂ)*A)).trans
    (add_le_add hIE hIG)
  have h := add_le_add he (mul_le_mul_of_nonneg_left hIH (norm_nonneg d))
  refine h.trans (le_of_eq ?_)
  dsimp only [C₃, M, coeff]
  ring

open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula (multiplicity_eq_zeroMult)
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData (zeroData_zero_on_critical_line_of_rh)

/-- Under RH an actual zero's rescaled mode is purely imaginary. -/
theorem window_mode_eq_ordinate (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : IsNontrivialZero z) :
    windowMode r z = (↑(z.im / r) : ℂ) * Complex.I := by
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hz
  have hre : z.re = 1/2 := by
    rw [← hn]
    simpa only [D5.S3.Weil.Convention.criticalAbscissa] using
      zeroData_zero_on_critical_line_of_rh hRH actualData n
  apply Complex.ext
  · simp [windowMode, Complex.div_re, hre]
  · simp [windowMode, Complex.div_im, Complex.normSq_ofReal]
    field_simp [hr.ne']

private theorem window_mode_ne_zero {r : ℝ} (hr : 0 < r) (k : ℕ) :
    windowMode r (actualZero k) ≠ 0 := by
  change frequency k / (r : ℂ) ≠ 0
  exact div_ne_zero (norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 10).trans (frequency_norm k)))
    (Complex.ofReal_ne_zero.mpr hr.ne')

/-- Testing the normalized signed residual at a fixed frequency recovers the entire matching
occurrence fiber. At an actual zero the fiber contributes its analytic multiplicity. -/
theorem signed_window_even_cutoff_fourier (hRH : RiemannHypothesis) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ m r : ℕ, 2 ≤ m → m+1 = 2*r →
      ∀ L : ℝ, 0 < L →
        let s := orderRate m
        let c := (μ (m+1) : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))
        let target := fun ω : ℝ => (if ω=0 then -(c : ℂ) else 0) - (μ r : ℂ) *
          (∑' k, if windowMode (r : ℝ) (actualZero k) = (ω : ℂ)*Complex.I
            then windowCoefficient (r : ℝ) L (actualZero k) else 0)
        (∀ ω : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ U T : ℝ, U₀ ≤ U → 0 < T →
          let F := fun u : ℝ => ((signedWindowResidual m (Real.exp u) (Real.exp (u+L)) /
            powerGap s (Real.exp u) (Real.exp (u+L)) : ℝ) : ℂ) *
              Complex.exp (-((ω : ℂ)*Complex.I)*(u : ℂ))
          IntervalIntegrable F volume U (U+T) ∧
          ‖(∫ u in U..U+T, F u)/(T : ℂ)-target ω‖ ≤ C/T) ∧
        target 0 = -(c : ℂ) ∧
        ∀ z : ℂ, IsNontrivialZero z →
          target (z.im/(r : ℝ)) =
            -(μ r : ℂ) * (Zeta23.zeroMult z : ℂ) * windowCoefficient (r : ℝ) L z ∧
          windowCoefficient (r : ℝ) L z ≠ 0 := by
  obtain ⟨U₀, hU₀, hbound⟩ := signed_window_even_cutoff_fourier_bound hRH
  refine ⟨U₀, hU₀, fun m r hm heven L hL => ⟨?_, ?_, ?_⟩⟩
  · intro ω
    obtain ⟨A, B, hA, hB, h⟩ := hbound m r hm heven ω
    refine ⟨A+B*(∑' k, ‖windowCoefficient (r : ℝ) L (actualZero k)‖), ?_, h L hL⟩
    exact add_pos_of_pos_of_nonneg hA (mul_nonneg hB (tsum_nonneg fun _ => norm_nonneg _))
  · have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    simp [window_mode_ne_zero hr]
  · intro z hz
    have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
    have hr0 : (0 : ℝ) < r := by linarith
    obtain ⟨n, hn⟩ := actualData.zero_exhaustive hz
    have hmode := window_mode_eq_ordinate hRH hr0 hz
    refine ⟨?_, window_coefficient_nonzero hRH hr hL hz⟩
    have hw : z.im/(r : ℝ) ≠ 0 := div_ne_zero
      (abs_pos.mp ((by norm_num : (0 : ℝ) < 10).trans (actual_height_gt_ten z hz))) hr0.ne'
    have hf := actual_frequency_multiplicity hr0 n (windowCoefficient (r : ℝ) L)
    rw [hn, multiplicity_eq_zeroMult, hn] at hf
    dsimp only
    rw [ite_eq_right hw, ← hmode]
    change 0 - (μ r : ℂ) *
        (∑' k, if frequency k/((r : ℝ) : ℂ) = (z-1/2)/((r : ℝ) : ℂ)
          then windowCoefficient (r : ℝ) L (actualZero k) else 0) = _
    rw [hf]
    ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
