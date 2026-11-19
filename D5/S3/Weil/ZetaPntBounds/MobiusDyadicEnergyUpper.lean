/- GID: D5/S3/Weil/ZetaPntBounds/MobiusDyadicEnergyUpper
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero-free half-planes bound the weighted Möbius energy and the normalized signed shells. -/

import D5.S3.Weil.Mertens.MobiusDyadicEnergy
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.LSeries.RiemannZeta
import D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import D5.S3.Weil.Mertens.LittlewoodUpstream.MathlibPR_ZetaInvSubpolynomial
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

/-!
The weighted energy proof transfers the normalized Fourier section of the
regularized reciprocal zeta function to real part `(α - 1) / 2`.
Weighted integrability then bounds the energy of each dyadic shell by a tail integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform Topology

namespace D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence

open D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
open D5.S3.Arith.MoebiusLogarithmic (reciprocalSum abs_reciprocalSum_le_one)
open D5.S3.Weil.Mertens.MobiusDyadicEnergy (mobiusDyadicDifference mobiusDyadicShellEnergy)

/-- The actual logarithmic weighted Möbius profile, extended by zero for negative time. -/
private def mobiusLogProfile (σ : ℝ) : ℝ → ℂ :=
  (Ici 0).indicator (fun t => (Real.exp (-σ * t) : ℂ) * (mobiusPartialSum (Real.exp t) : ℂ))

private theorem measurable_mobiusPartialSum : Measurable mobiusPartialSum := by
  exact (measurable_of_countable
    (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))).comp
    Nat.measurable_floor

private theorem measurable_mobiusLogProfile (σ : ℝ) : Measurable (mobiusLogProfile σ) := by
  have he : Measurable (fun t : ℝ => (Real.exp (-σ * t) : ℂ)) := by fun_prop
  have hm : Measurable (fun t : ℝ => (mobiusPartialSum (Real.exp t) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_mobiusPartialSum.comp Real.continuous_exp.measurable)
  exact (he.mul hm).indicator measurableSet_Ici

private theorem mobiusLogProfile_eq_zero (σ : ℝ) {t : ℝ} (ht : t < 0) :
    mobiusLogProfile σ t = 0 :=
  indicator_of_notMem (show t ∉ Ici (0 : ℝ) from not_le.mpr ht) _

private theorem ae_continuousAt_mobiusLogProfile (σ : ℝ) :
    ∀ᵐ t ∂(volume : Measure ℝ), ContinuousAt (mobiusLogProfile σ) t := by
  let J := Set.range (fun n : ℕ => Real.log (n : ℝ))
  have hJ : J.Countable := Set.countable_range _
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ J := by
    exact compl_mem_ae_iff.mpr (hJ.measure_zero volume)
  filter_upwards [hae] with t ht
  have ht_ne : t ≠ 0 := by
    intro he
    apply ht
    exact ⟨1, by simpa using he.symm⟩
  rcases lt_or_gt_of_ne ht_ne with ht₀ | ht₀
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [eventually_lt_nhds ht₀] with u hu
    exact (mobiusLogProfile_eq_zero σ hu).symm
  · let k := ⌊Real.exp t⌋₊
    have hlow : (k : ℝ) < Real.exp t := by
      apply lt_of_le_of_ne (Nat.floor_le (Real.exp_nonneg t))
      intro hk
      exact ht ⟨k, by
        change Real.log (k : ℝ) = t
        rw [hk, Real.log_exp]⟩
    have hhigh : Real.exp t < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have he : ContinuousAt (fun u : ℝ => (Real.exp (-σ * u) : ℂ) *
        (mobiusPartialSum (Real.exp t) : ℂ)) t := by
      fun_prop
    refine he.congr ?_
    filter_upwards [eventually_gt_nhds ht₀,
      Real.continuous_exp.continuousAt.eventually (eventually_gt_nhds hlow),
      Real.continuous_exp.continuousAt.eventually (eventually_lt_nhds hhigh)]
      with u hu hku huk
    have hfloor : ⌊Real.exp u⌋₊ = k :=
      (Nat.floor_eq_iff (Real.exp_nonneg u)).mpr ⟨hku.le, huk⟩
    have hsum : mobiusPartialSum (Real.exp u) = mobiusPartialSum (Real.exp t) := by
      unfold mobiusPartialSum
      rw [hfloor]
    rw [mobiusLogProfile, indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu.le), hsum]

private theorem norm_mobiusPartialSum_le_one (x : ℝ) :
    ‖(mobiusPartialSum x : ℂ)‖ ≤ 1 := by
  have he : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simpa only [Complex.norm_real, Real.norm_eq_abs, mobiusPartialSum, reciprocalSum, he] using
    abs_reciprocalSum_le_one x

private theorem norm_mobiusLogProfile_of_nonneg (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖mobiusLogProfile σ t‖ =
      Real.exp (-σ * t) * ‖(mobiusPartialSum (Real.exp t) : ℂ)‖ := by
  rw [mobiusLogProfile, indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]

private theorem bounded_mobiusLogProfile (σ : ℝ) (T : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Icc 0 T, ‖mobiusLogProfile σ t‖ ≤ M := by
  refine ⟨Real.exp (|σ| * T), fun t ht => ?_⟩
  rw [norm_mobiusLogProfile_of_nonneg σ ht.1]
  have hexp : Real.exp (-σ * t) ≤ Real.exp (|σ| * T) :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (neg_le_abs σ) ht.1).trans
      (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg σ)))
  exact (mul_le_of_le_one_right (Real.exp_nonneg _) (norm_mobiusPartialSum_le_one _)).trans hexp

private theorem integrable_mobiusLogProfile_one : Integrable (mobiusLogProfile 1) := by
  let f : ℝ → ℝ := fun t => Real.exp (-(1 : ℝ) * t)
  have hfOn : IntegrableOn f (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by norm_num : -(1 : ℝ) < 0) 0
  have hf : Integrable ((Ici (0 : ℝ)).indicator f) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr hfOn).integrable_indicator measurableSet_Ici
  refine hf.mono' (measurable_mobiusLogProfile 1).aestronglyMeasurable ?_
  filter_upwards with t
  by_cases ht : 0 ≤ t
  · rw [indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht), norm_mobiusLogProfile_of_nonneg 1 ht]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) (norm_mobiusPartialSum_le_one _)
  · rw [mobiusLogProfile_eq_zero 1 (lt_of_not_ge ht), norm_zero,
      indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht)]

private theorem tilt_mobiusLogProfile_one (σ : ℝ) :
    tilt (1 - σ) (mobiusLogProfile σ) = mobiusLogProfile 1 := by
  funext t
  by_cases ht : t ∈ Ici (0 : ℝ)
  · simp only [tilt, mobiusLogProfile, indicator_of_mem ht]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      show -(1 - σ) * t + -σ * t = -(1 : ℝ) * t by ring]
  · simp [tilt, mobiusLogProfile, ht]

private theorem exp_smul_mobiusMellinIntegrand (s : ℂ) (t : ℝ) :
    Real.exp t • ((mobiusPartialSum (Real.exp t) : ℂ) * (Real.exp t : ℂ) ^ (-(s + 1))) =
      Complex.exp (-s * (t : ℂ)) * (mobiusPartialSum (Real.exp t) : ℂ) := by
  have hn : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (Real.exp_nonneg t),
    Real.log_exp, Complex.real_smul, Complex.ofReal_exp]
  calc
    _ = (Complex.exp (t : ℂ) * Complex.exp ((t : ℂ) * -(s + 1))) *
        (mobiusPartialSum (Real.exp t) : ℂ) := by ring
    _ = _ := by
      rw [← Complex.exp_add, show (t : ℂ) + (t : ℂ) * -(s + 1) = -s * (t : ℂ) by ring]

private theorem fourier_mobiusLogProfile_one :
    𝓕 (mobiusLogProfile 1) = sectionAt regularizedZetaReciprocal 1 := by
  funext ξ
  let s : ℂ := (1 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
  change 𝓕 (mobiusLogProfile 1) ξ = regularizedZetaReciprocal s
  have hs_re : s.re = 1 := by simp [s, Complex.add_re, Complex.mul_re]
  have hs_pos : 0 < s.re := by rw [hs_re]; exact zero_lt_one
  have hs : s ≠ 0 := by
    intro hz
    simp [hz] at hs_pos
  have hphase (t : ℝ) :
      ((-2 * Real.pi * (t * ξ) : ℝ) : ℂ) * I + ((-(1 : ℝ) * t : ℝ) : ℂ) =
        -s * (t : ℂ) := by
    dsimp [s]
    push_cast
    ring
  calc
    𝓕 (mobiusLogProfile 1) ξ =
        ∫ t : ℝ, (Ici (0 : ℝ)).indicator
          (fun u : ℝ => Complex.exp (-s * (u : ℂ)) *
            (mobiusPartialSum (Real.exp u) : ℂ)) t := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with t
      simp only [Real.inner_apply, smul_eq_mul]
      by_cases ht : t ∈ Ici (0 : ℝ)
      · simp only [mobiusLogProfile, indicator_of_mem ht, Complex.ofReal_exp]
        rw [← mul_assoc, ← Complex.exp_add, hphase]
      · simp [mobiusLogProfile, ht]
    _ = ∫ t : ℝ in Ioi 0, Real.exp t • ((mobiusPartialSum (Real.exp t) : ℂ) *
          (Real.exp t : ℂ) ^ (-(s + 1))) := by
      rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t _ => (exp_smul_mobiusMellinIntegrand s t).symm)
    _ = mobiusMellin s := by
      simpa only [Real.exp_zero, mobiusMellin] using
        (integral_comp_exp_Ioi (fun x : ℝ => (mobiusPartialSum x : ℂ) *
          (x : ℂ) ^ (-(s + 1))) 0)
    _ = regularizedZetaReciprocal s := by
      rw [regularizedZetaReciprocal_eq hs, add_comm (1 : ℂ) s]
      have hz : riemannZeta (s + 1) ≠ 0 :=
        riemannZeta_ne_zero_of_one_lt_re (by simpa using hs_pos)
      apply (eq_div_iff (mul_ne_zero hs hz)).mpr
      calc
        mobiusMellin s * (s * riemannZeta (s + 1)) =
            (s * mobiusMellin s) * riemannZeta (s + 1) := by ring
        _ = 1 := by rw [initial_mellin_identity hs_pos, one_div, inv_mul_cancel₀ hz]

private theorem memLp_sectionAt_of_decay_threeQuarters {σ C : ℝ} {F : ℂ → ℂ}
    (hcont : Continuous (fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I)))
    (hdecay : ∀ y : ℝ, ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-(3 / 4 : ℝ))) :
    MemLp (sectionAt F σ) 2 := by
  have hmajor : Integrable (fun y : ℝ => C ^ 2 * (1 + |y|) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)).const_mul
        (C ^ 2)
  have hsq : Integrable (fun y : ℝ => ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) := by
    refine hmajor.mono' (hcont.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (C * (1 + |y|) ^ (-(3 / 4 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdecay y) 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + |y|)]
        norm_num
  have hπ : 0 < 2 * Real.pi := by positivity
  have hscale : Continuous (fun ξ : ℝ => 2 * Real.pi * ξ) := by fun_prop
  change MemLp (fun ξ : ℝ => F ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) 2
  exact (memLp_two_iff_integrable_sq_norm
    (hcont.comp hscale).aestronglyMeasurable).2 (hsq.comp_mul_left' hπ.ne')

/-- Arithmetic specialization of the abstract strip transfer. -/
private theorem mobiusLogProfile_memLp_of_zero_free {θ α : ℝ}
    (hθ_half : 1 / 2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hα_lo : 2 * θ - 1 < α) (hα_hi : α < 1) :
    MemLp (mobiusLogProfile ((α - 1) / 2)) 2 := by
  let σ : ℝ := (α - 1) / 2
  have hσ : θ - 1 < σ := by dsimp [σ]; linarith
  have hσ₁ : σ < 1 := by dsimp [σ]; linarith
  obtain ⟨C, hC, hC_bound⟩ := norm_regularizedZetaReciprocal_le_rpow_of_zero_free
    (σ₀ := 1) (p := 3 / 4) hθ_half hθ_lt_one hzero hσ (by norm_num) (by norm_num)
  have hOpen : IsOpen {z : ℂ | θ - 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff := differentiableOn_regularizedZetaReciprocal_of_zero_free hθ_lt_one hzero
  have hF (z : ℂ) (hz : z.re ∈ Icc σ 1) :
      DifferentiableAt ℂ regularizedZetaReciprocal z :=
    (hdiff z (hσ.trans_le hz.1)).differentiableAt (hOpen.mem_nhds (hσ.trans_le hz.1))
  have hdecay : ∀ a ∈ Icc σ 1, ∀ y : ℝ,
      ‖regularizedZetaReciprocal ((a : ℂ) + (y : ℂ) * I)‖ ≤
        C * (1 + |y|) ^ (-(3 / 4 : ℝ)) := by
    intro a ha y
    have hre : ((a : ℂ) + (y : ℂ) * I).re = a := by
      simp [Complex.add_re, Complex.mul_re]
    have him : ((a : ℂ) + (y : ℂ) * I).im = y := by
      simp [Complex.add_im, Complex.mul_im]
    simpa only [him] using
      (hC_bound ((a : ℂ) + (y : ℂ) * I) (by rw [hre]; exact ha.1)
        (by rw [hre]; exact ha.2))
  have hsection : Continuous (fun y : ℝ => regularizedZetaReciprocal
      ((σ : ℂ) + (y : ℂ) * I)) := by
    have hline : Continuous (fun y : ℝ => (σ : ℂ) + (y : ℂ) * I) := by fun_prop
    exact hdiff.continuousOn.comp_continuous hline (fun y => by
      change θ - 1 < ((σ : ℂ) + (y : ℂ) * I).re
      simpa [Complex.add_re, Complex.mul_re] using hσ)
  exact memLp_of_strip_transfer (σ := σ) (σ₀ := 1) (p := 3 / 4) hσ₁ hC.le
    (by norm_num) hF hdecay (measurable_mobiusLogProfile σ)
    (ae_continuousAt_mobiusLogProfile σ) (fun t ht => mobiusLogProfile_eq_zero σ ht)
    (bounded_mobiusLogProfile σ)
    (by rw [tilt_mobiusLogProfile_one]; exact integrable_mobiusLogProfile_one)
    (by rw [tilt_mobiusLogProfile_one]; exact fourier_mobiusLogProfile_one)
    (memLp_sectionAt_of_decay_threeQuarters hsection (hdecay σ ⟨le_rfl, hσ₁.le⟩))

/-- Finite weighted energy of the literal sum on the Lebesgue half-line. -/
theorem mobiusPartialSum_weightedEnergy_integrable_of_zero_free {θ α : ℝ}
    (hθ_half : 1 / 2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hα_lo : 2 * θ - 1 < α) (hα_hi : α < 1) :
    IntegrableOn (fun x : ℝ => mobiusPartialSum x ^ 2 * x ^ (-α)) (Ioi 1) := by
  let σ : ℝ := (α - 1) / 2
  let f : ℝ → ℝ := fun x => mobiusPartialSum x ^ 2 * x ^ (-α)
  have hg : MemLp (mobiusLogProfile σ) 2 :=
    mobiusLogProfile_memLp_of_zero_free hθ_half hθ_lt_one hzero hα_lo hα_hi
  have hsq := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hsub : IntegrableOn (fun t : ℝ => Real.exp t • f (Real.exp t)) (Ioi 0) := by
    refine hsq.integrableOn.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    rw [norm_mobiusLogProfile_of_nonneg σ (le_of_lt ht), Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    change Real.exp (-σ * t) ^ 2 * mobiusPartialSum (Real.exp t) ^ 2 =
      Real.exp t * (mobiusPartialSum (Real.exp t) ^ 2 * (Real.exp t) ^ (-α))
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_nat_mul (-σ * t) 2]
    calc
      _ = mobiusPartialSum (Real.exp t) ^ 2 * Real.exp ((2 : ℝ) * (-σ * t)) := by
        norm_num [mul_comm]
      _ = mobiusPartialSum (Real.exp t) ^ 2 * Real.exp (t + t * -α) := by
        rw [show (2 : ℝ) * (-σ * t) = t + t * -α by dsimp [σ]; ring]
      _ = _ := by rw [Real.exp_add]; ring
  simpa only [Real.exp_zero, f] using (integrableOn_comp_exp_Ioi f 0).mp hsub

private theorem measurable_mobiusDyadicDifference : Measurable mobiusDyadicDifference :=
  measurable_mobiusPartialSum.sub (measurable_mobiusPartialSum.comp (by fun_prop))

/-- Dilation preserves weighted integrability of the squared partial sum. -/
private theorem mobiusPartialSum_weightedEnergy_dilate {α : ℝ}
    (hm : IntegrableOn (fun x : ℝ => mobiusPartialSum x ^ 2 * x ^ (-α)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => mobiusPartialSum (2 * x) ^ 2 * x ^ (-α)) (Ioi 1) := by
  let f : ℝ → ℝ := fun x => mobiusPartialSum x ^ 2 * x ^ (-α)
  have h₂ : IntegrableOn f (Ioi ((2 : ℝ) * 1)) := hm.mono_set
    (Ioi_subset_Ioi (by norm_num))
  have hd := (integrableOn_Ioi_comp_mul_left_iff f 1 (by norm_num : 0 < (2 : ℝ))).mpr h₂
  refine (hd.const_mul ((2 : ℝ) ^ α)).congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
  have hx₀ : 0 ≤ x := zero_le_one.trans (le_of_lt hx)
  have hcancel : (2 : ℝ) ^ α * (2 : ℝ) ^ (-α) = 1 := by
    rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ)), add_neg_cancel, Real.rpow_zero]
  change (2 : ℝ) ^ α * (mobiusPartialSum (2 * x) ^ 2 * (2 * x) ^ (-α)) = _
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hx₀]
  calc
    _ = ((2 : ℝ) ^ α * (2 : ℝ) ^ (-α)) *
          (mobiusPartialSum (2 * x) ^ 2 * x ^ (-α)) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- Finite weighted energy of the literal signed difference on x > 1. -/
theorem mobiusDyadicDifference_weightedEnergy_integrable_of_zero_free {θ α : ℝ}
    (hθ_half : 1 / 2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hα_lo : 2 * θ - 1 < α) (hα_hi : α < 1) :
    IntegrableOn (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-α)) (Ioi 1) := by
  have hm := mobiusPartialSum_weightedEnergy_integrable_of_zero_free
    hθ_half hθ_lt_one hzero hα_lo hα_hi
  have hd := mobiusPartialSum_weightedEnergy_dilate hm
  refine ((hm.add hd).const_mul (2 : ℝ)).mono' ?_ ?_
  · exact ((measurable_mobiusDyadicDifference.pow_const 2).mul
      (by fun_prop : Measurable (fun x : ℝ => x ^ (-α)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
    have hw : 0 ≤ x ^ (-α) := Real.rpow_nonneg (zero_le_one.trans (le_of_lt hx)) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw)]
    have hs : mobiusDyadicDifference x ^ 2 ≤
        2 * (mobiusPartialSum x ^ 2 + mobiusPartialSum (2 * x) ^ 2) := by
      unfold mobiusDyadicDifference
      nlinarith [sq_nonneg (mobiusPartialSum x + mobiusPartialSum (2 * x))]
    calc
      _ ≤ (2 * (mobiusPartialSum x ^ 2 + mobiusPartialSum (2 * x) ^ 2)) * x ^ (-α) :=
        mul_le_mul_of_nonneg_right hs hw
      _ = _ := by
        change _ = 2 * (mobiusPartialSum x ^ 2 * x ^ (-α) +
          mobiusPartialSum (2 * x) ^ 2 * x ^ (-α))
        ring

/-- Normalized signed shell energy tends to zero throughout the open exponent range. -/
theorem mobiusDyadicShellEnergy_normalized_tendsto_zero_of_zero_free {θ α : ℝ}
    (hθ_half : 1 / 2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hα_lo : 2 * θ - 1 < α) (hα_hi : α < 1) :
    Tendsto (fun k : ℕ => mobiusDyadicShellEnergy k / (((2 : ℝ) ^ k) ^ α))
      atTop (𝓝 0) := by
  let f : ℝ → ℝ := fun x => mobiusDyadicDifference x ^ 2 * x ^ (-α)
  have hf : IntegrableOn f (Ioi (1 : ℝ)) :=
    mobiusDyadicDifference_weightedEnergy_integrable_of_zero_free
      hθ_half hθ_lt_one hzero hα_lo hα_hi
  have hα : 0 ≤ α := by linarith
  have hb : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have htail : Tendsto (fun k : ℕ => ∫ x in Ioi ((2 : ℝ) ^ k), f x) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero hb
  have hlim : Tendsto (fun k : ℕ => (2 : ℝ) ^ α *
      ∫ x in Ioi ((2 : ℝ) ^ k), f x) atTop (𝓝 0) := by
    simpa only [mul_zero] using htail.const_mul ((2 : ℝ) ^ α)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun k =>
      div_nonneg (integral_nonneg (fun x => sq_nonneg (mobiusDyadicDifference x))) (by positivity)
  · filter_upwards [hb.eventually (eventually_ge_atTop (1 : ℝ))] with k hk
    let a : ℝ := (2 : ℝ) ^ k
    let b : ℝ := (2 : ℝ) ^ (k + 1)
    let w : ℝ := b ^ (-α)
    have ha : 1 ≤ a := hk
    have ha₀ : 0 < a := zero_lt_one.trans_le ha
    have hb₀ : 0 < b := by dsimp [b]; positivity
    have hw : 0 < w := Real.rpow_pos_of_pos hb₀ _
    have htailInt : IntegrableOn f (Ioi a) := hf.mono_set (Ioi_subset_Ioi ha)
    have hShellInt : IntegrableOn f (Ioc a b) := htailInt.mono_set Ioc_subset_Ioi_self
    have hweight (x : ℝ) (hx : x ∈ Ioc a b) : w ≤ x ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (ha₀.trans hx.1) hx.2 (neg_nonpos.mpr hα)
    have hconstInt : IntegrableOn (fun x => w * mobiusDyadicDifference x ^ 2) (Ioc a b) := by
      refine hShellInt.mono'
        ((measurable_mobiusDyadicDifference.pow_const (2 : ℕ)).const_mul w).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := a) (b := b))] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw.le (sq_nonneg _))]
      simpa only [f, mul_comm] using mul_le_mul_of_nonneg_right (hweight x hx) (sq_nonneg (mobiusDyadicDifference x))
    have hmass : w * mobiusDyadicShellEnergy k ≤ ∫ x in Ioi a, f x := by
      calc
        _ = ∫ x in Ioc a b, w * mobiusDyadicDifference x ^ 2 := by
          rw [mobiusDyadicShellEnergy, integral_const_mul]
        _ ≤ ∫ x in Ioc a b, f x :=
          setIntegral_mono_on hconstInt hShellInt measurableSet_Ioc (fun x hx => by
            simpa only [f, mul_comm] using
              mul_le_mul_of_nonneg_right (hweight x hx) (sq_nonneg (mobiusDyadicDifference x)))
        _ ≤ ∫ x in Ioi a, f x := by
          refine setIntegral_mono_set htailInt ?_ Ioc_subset_Ioi_self.eventuallySubset
          filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := a))] with x hx
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (ha₀.trans hx).le _)
    have hscale : (2 : ℝ) ^ α * w = (a ^ α)⁻¹ := by
      have hb_eq : b = a * 2 := pow_succ (2 : ℝ) k
      rw [show w = b ^ (-α) from rfl, hb_eq, Real.mul_rpow ha₀.le (by norm_num)]
      rw [mul_left_comm, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ)),
        add_neg_cancel, Real.rpow_zero, mul_one, Real.rpow_neg ha₀.le]
    calc
      _ = (2 : ℝ) ^ α * (w * mobiusDyadicShellEnergy k) := by
        rw [← mul_assoc, hscale, div_eq_mul_inv]
        exact mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

#print axioms mobiusPartialSum_weightedEnergy_integrable_of_zero_free
#print axioms mobiusDyadicDifference_weightedEnergy_integrable_of_zero_free
#print axioms mobiusDyadicShellEnergy_normalized_tendsto_zero_of_zero_free

end D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
