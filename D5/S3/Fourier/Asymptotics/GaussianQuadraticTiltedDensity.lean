/- GID: D5/S3/Fourier/Asymptotics/GaussianQuadraticTiltedDensity
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/GaussianQuadraticTiltedDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact lower bounds for physical tilted Gaussian quadratic densities. -/

import D5.S3.TotalVariation.Asymptotics.StatLeanFourierSuppliers
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Complex Finset
open scoped NNReal ENNReal Topology FourierTransform RealInnerProductSpace

namespace D5.S3.Fourier.Asymptotics.GaussianQuadraticTiltedDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- A core of small positive variances gives a uniform compact lower bound for the
actual tilted energy convolution. The full signed saddle includes the noise mean. -/
theorem result (κ K R : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hK : 1 ≤ K) (hR : 0 ≤ R) :
    ∃ δ₀ c : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < c ∧
    ∀ (J : Type u) [Fintype J] [DecidableEq J] (H Core : Finset J)
      (v e : J → ℝ) (δ σ α t : ℝ),
    0 < δ → δ ≤ δ₀ → 0 < σ → σ ≤ 1 → α ∈ Set.Icc (1 : ℝ) 2 →
    (∀ j, 0 ≤ v j) → (∀ j ∈ H, 0 < v j) →
    let V := ∑ j, v j
    let d : J → ℝ := fun j => 1 - 2 * t * v j / α
    κ ≤ V → V ≤ K → (∀ j, v j ≤ K * δ) →
    Core ⊆ H → κ / δ ≤ (Core.card : ℝ) →
    (∀ j ∈ Core, κ * δ ≤ v j) →
    (H.card : ℝ) ≤ K * δ ^ (-4 : ℤ) →
    (∀ j, |e j| ≤ K * Real.sqrt (v j) * δ ^ 2) →
    (∀ j, d j ∈ Set.Icc κ K) → |t| ≤ K / δ →
    (∑ j, v j / (α * d j)) + (∑ j, e j ^ 2 / d j ^ 2) +
      δ * σ ^ 2 * t / α = V →
    (∑ j ∈ univ \ H, (v j + e j ^ 2)) ≤ δ ^ 2 →
    let ν : ℝ := δ * σ ^ 2 / α
    let P : Measure (H → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
    let Xt : (H → ℝ) → H → ℝ :=
      fun z j => Real.sqrt (v j / (α * d j)) * z j - e j / d j
    let E : (H → ℝ) → ℝ := fun x => ∑ j, x j ^ 2
    ∀ y : ℝ, |y| ≤ R →
    let h := V + Real.sqrt δ * y
    let gt := ∫ z, gaussianPDFReal (ν * t) (ν.toNNReal) (h - E (Xt z)) ∂P
    c / Real.sqrt δ ≤ gt := by
  classical
  have hbern (δ A B ξ : ℝ) (hδ : 0 < δ) (hA : 0 < A) (hB : 0 < B)
      (hsmall : δ ≤ B / 8) :
      (1 + A * δ * ξ ^ 2) ^ (-(B / δ)) ≤
        (1 + A * B * ξ ^ 2 / 8) ^ (-(8 : ℝ)) := by
    clear * - δ A B ξ hδ hA hB hsmall
    have hp : 1 ≤ B / (8 * δ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hb := one_add_mul_self_le_rpow_one_add
      (s := A * δ * ξ ^ 2)
      (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (by positivity)) hp
    have he : 1 + B / (8 * δ) * (A * δ * ξ ^ 2) =
        1 + A * B * ξ ^ 2 / 8 := by field_simp
    rw [he] at hb
    have hb8 := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + A * B * ξ ^ 2 / 8)
      hb (by norm_num : (0 : ℝ) ≤ 8)
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + A * δ * ξ ^ 2)] at hb8
    have hep : B / (8 * δ) * 8 = B / δ := by ring
    rw [hep] at hb8
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + A * δ * ξ ^ 2),
      Real.rpow_neg (by positivity : 0 ≤ 1 + A * B * ξ ^ 2 / 8)]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr hb8
  have hscalarLog (a b ξ : ℝ) :
      charFun ((gaussianReal 0 1).map (fun z => a * (z ^ 2 - 1) + b * z)) ξ =
      Complex.exp (-(ξ : ℂ) * (a : ℂ) * Complex.I -
        Complex.log (1 - 2 * (ξ : ℂ) * (a : ℂ) * Complex.I) / 2 -
        ((ξ : ℂ) * (b : ℂ)) ^ 2 / (2 * (1 - 2 * (ξ : ℂ) * (a : ℂ) * Complex.I))) := by
    clear * - a b ξ
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    simp_rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
      Complex.real_smul, gaussianPDFReal]
    push_cast
    simp only [sub_zero, mul_one]
    simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
    have he (x : ℝ) : -((x : ℂ) ^ 2) / 2 +
        (ξ : ℂ) * (((a : ℂ) * ((x : ℂ) ^ 2 - 1) + (b : ℂ) * x) * Complex.I) =
        ((ξ : ℂ) * a * Complex.I - 1 / 2) * x ^ 2 +
          ((ξ : ℂ) * b * Complex.I) * x + -((ξ : ℂ) * a * Complex.I) := by ring
    simp_rw [he]
    rw [integral_cexp_quadratic (b := (ξ : ℂ) * a * Complex.I - 1 / 2)
      (by norm_num [Complex.mul_re, Complex.mul_im]) ((ξ : ℂ) * b * Complex.I)
      (-((ξ : ℂ) * a * Complex.I))]
    rw [show -((ξ : ℂ) * a * Complex.I - 1 / 2) =
      1 / 2 - (ξ : ℂ) * a * Complex.I by ring]
    rw [show 4 * ((ξ : ℂ) * a * Complex.I - 1 / 2) =
      -(2 * (1 - 2 * (ξ : ℂ) * a * Complex.I)) by ring]
    simp only [mul_pow, Complex.I_sq, mul_neg_one, div_neg, neg_div, neg_neg]
    let z : ℂ := 1 - 2 * (ξ : ℂ) * (a : ℂ) * Complex.I
    have hzre : z.re = 1 := by simp [z, mul_re, mul_im]
    have hz : z ≠ 0 := by intro h; simp [h] at hzre
    have hbranch : z.arg ≠ Real.pi :=
      Complex.slitPlane_arg_ne_pi (Or.inl (by simp [hzre] : (0 : ℝ) < z.re))
    have hpi : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hratio : Real.pi / (1 / 2 - (ξ : ℂ) * (a : ℂ) * Complex.I) =
        (2 * Real.pi : ℝ) * z⁻¹ := by
      dsimp [z]
      push_cast
      field_simp
    have hpz : (↑(2 * Real.pi) : ℂ) * z⁻¹ ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hpi.ne') (inv_ne_zero hz)
    rw [hratio, Complex.cpow_def_of_ne_zero hpz,
      Complex.log_ofReal_mul hpi (inv_ne_zero hz), Complex.log_inv z hbranch]
    rw [show ((Real.log (2 * Real.pi) : ℂ) + -Complex.log z) * (1 / 2 : ℂ) =
      (Real.log (2 * Real.pi) : ℂ) / 2 - Complex.log z / 2 by ring]
    rw [sub_eq_add_neg, Complex.exp_add]
    have hsqrt : Complex.exp ((Real.log (2 * Real.pi) : ℂ) / 2) =
        (Real.sqrt (2 * Real.pi) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpi]
      push_cast
      congr 1
      ring
    rw [hsqrt]
    have hs0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpi).ne'
    simp only [← mul_assoc, inv_mul_cancel₀ hs0, one_mul, ← Complex.exp_add]
    congr 1
    dsimp [z]
    ring
  have hscalarNorm (a b ξ : ℝ) :
      ‖charFun ((gaussianReal 0 1).map (fun z => a * (z ^ 2 - 1) + b * z)) ξ‖ ≤
        (1 + 4 * ξ ^ 2 * a ^ 2) ^ (-(1 / 4 : ℝ)) := by
    clear * - a b ξ hscalarLog
    rw [hscalarLog, Complex.norm_exp]
    let z : ℂ := 1 - 2 * (ξ : ℂ) * (a : ℂ) * Complex.I
    have hzre : z.re = 1 := by simp [z, mul_re, mul_im]
    have hn : ‖z‖ ^ 2 = 1 + 4 * ξ ^ 2 * a ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq, z, mul_re, mul_im]
      ring
    have hl : Real.log ‖z‖ = Real.log (1 + 4 * ξ ^ 2 * a ^ 2) / 2 := by
      rw [← hn, Real.log_pow]
      ring
    have hnoncentral : 0 ≤ (((ξ : ℂ) * (b : ℂ)) ^ 2 / (2 * z)).re := by
      rw [show ((ξ : ℂ) * (b : ℂ)) ^ 2 = (((ξ * b) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
        Complex.div_re]
      simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
      exact div_nonneg (mul_nonneg (sq_nonneg _) (by simp [z, mul_re, mul_im]))
        (Complex.normSq_nonneg _)
    have hr : (-(ξ : ℂ) * (a : ℂ) * Complex.I - Complex.log z / 2 -
        ((ξ : ℂ) * (b : ℂ)) ^ 2 / (2 * z)).re ≤ -Real.log ‖z‖ / 2 := by
      simp only [sub_re, div_ofNat_re, Complex.log_re]
      have hi : (-(ξ : ℂ) * (a : ℂ) * Complex.I).re = 0 := by simp [mul_re, mul_im]
      rw [hi]
      linarith
    calc
      _ ≤ Real.exp (-Real.log ‖z‖ / 2) := Real.exp_le_exp.mpr hr
      _ = _ := by
        rw [hl, Real.rpow_def_of_pos (by positivity : 0 < 1 + 4 * ξ ^ 2 * a ^ 2)]
        congr 1
        ring
  have harrayEnvelope {I : Type u} [Fintype I] (a b : I → ℝ)
      (γ δ A B : ℝ) (Core : Finset I) (hδ : 0 < δ)
      (hA : 0 < A) (hB : 0 < B) (hsmall : δ ≤ B / 32)
      (hcard : B / δ ≤ (Core.card : ℝ)) (hcore : ∀ j ∈ Core, A * δ ≤ a j ^ 2)
      (ξ : ℝ) :
      ‖Complex.exp (-((γ : ℂ) * ξ) ^ 2 / 2) *
        ∏ j, charFun ((gaussianReal 0 1).map
          (fun z => a j * (z ^ 2 - 1) + b j * z)) ξ‖ ≤
        (1 + A * B * ξ ^ 2 / 8) ^ (-(8 : ℝ)) := by
    clear * - I a b γ δ A B Core hδ hA hB hsmall hcard hcore ξ hscalarNorm hbern
    let f : I → ℝ := fun j =>
      ‖charFun ((gaussianReal 0 1).map (fun z => a j * (z ^ 2 - 1) + b j * z)) ξ‖
    have hf1 (j : I) : f j ≤ 1 := by
      have : IsProbabilityMeasure ((gaussianReal 0 1).map
        (fun z => a j * (z ^ 2 - 1) + b j * z)) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      exact norm_charFun_le_one _
    have hprod : (∏ j, f j) ≤ ∏ j ∈ Core, f j :=
      prod_le_prod_of_subset_of_le_one (subset_univ Core)
        (fun j _ => norm_nonneg _) (fun j _ _ => hf1 j)
    have hcoreProd : (∏ j ∈ Core, f j) ≤
        (1 + 4 * A * δ * ξ ^ 2) ^ (-(Core.card : ℝ) / 4) := by
      calc
        _ ≤ ∏ _j ∈ Core, (1 + 4 * A * δ * ξ ^ 2) ^ (-(1 / 4 : ℝ)) := by
          apply prod_le_prod (fun j _ => norm_nonneg _)
          intro j hj
          exact (hscalarNorm (a j) (b j) ξ).trans
            (Real.rpow_le_rpow_of_nonpos (by positivity)
              (by nlinarith [mul_le_mul_of_nonneg_left (hcore j hj) (sq_nonneg ξ)])
              (by norm_num))
        _ = _ := by
          rw [prod_const, ← Real.rpow_mul_natCast (by positivity)]
          congr 1
          ring
    have hexp : ‖Complex.exp (-((γ : ℂ) * ξ) ^ 2 / 2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simp only [← ofReal_mul, ← ofReal_pow, ← ofReal_neg, ← ofReal_ofNat,
        ← ofReal_div, ofReal_re]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
    rw [norm_mul, norm_prod]
    calc
      _ ≤ 1 * ∏ j, f j := mul_le_mul_of_nonneg_right hexp (prod_nonneg fun _ _ => norm_nonneg _)
      _ ≤ (1 + 4 * A * δ * ξ ^ 2) ^ (-(Core.card : ℝ) / 4) := by
        simpa only [one_mul] using hprod.trans hcoreProd
      _ ≤ (1 + 4 * A * δ * ξ ^ 2) ^ (-(B / 4 / δ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by
          have hh : 0 ≤ 4 * A * δ * ξ ^ 2 := by positivity
          linarith)
        have hh := div_le_div_of_nonneg_right hcard (by norm_num : (0 : ℝ) ≤ 4)
        rw [show B / 4 / δ = B / δ / 4 by ring]
        simpa only [neg_div] using neg_le_neg hh
      _ ≤ _ := by
        convert hbern δ (4 * A) (B / 4) ξ hδ (by positivity) (by positivity)
          (by linarith) using 2 <;> ring
  have hfiniteTransform {I : Type u} [Fintype I] (a b : I → ℝ) (ξ : ℝ) :
      charFun ((Measure.pi (fun _ : I => gaussianReal 0 1)).map
        (fun z => ∑ j, (a j * (z j ^ 2 - 1) + b j * z j))) ξ =
        ∏ j, charFun ((gaussianReal 0 1).map
          (fun z => a j * (z ^ 2 - 1) + b j * z)) ξ := by
    clear * - I a b ξ
    haveI (j : I) : IsProbabilityMeasure ((gaussianReal 0 1).map
        (fun z => a j * (z ^ 2 - 1) + b j * z)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hs := congrFun (charFun_map_sum_pi_eq_prod (fun j : I =>
      (gaussianReal 0 1).map (fun z => a j * (z ^ 2 - 1) + b j * z))) ξ
    rw [← Measure.pi_map_pi (fun _ => by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at hs
    simpa only [Function.comp_def, Finset.prod_apply] using hs
  have hEnvelope (c : ℝ) (hc : 0 < c) :
      Integrable (fun ξ : ℝ => (1 + c * ξ ^ 2) ^ (-(8 : ℝ))) := by
    clear * - c hc
    have hi := integrable_rpow_neg_one_add_norm_sq
      (E := ℝ) (μ := (volume : Measure ℝ)) (r := 16) (by norm_num)
    have hs := hi.comp_mul_left' (Real.sqrt_pos.mpr hc).ne'
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hc.le,
      show -(16 : ℝ) / 2 = -8 by norm_num] using hs
  have herrorIntegral (c : ℝ) (hc : 0 < c) :
      Filter.Tendsto (fun n : ℕ => ∫ ξ : ℝ,
        min (((3 : ℝ) / (n + 1) * |ξ| ^ 3) * Real.exp (3 / (n + 1) * |ξ| ^ 3))
          (2 * (1 + c * ξ ^ 2) ^ (-(8 : ℝ)) + Real.exp (-ξ ^ 2 / 2)))
        Filter.atTop (𝓝 0) := by
    clear * - c hc hEnvelope
    let G : ℝ → ℝ := fun ξ => 2 * (1 + c * ξ ^ 2) ^ (-(8 : ℝ)) + Real.exp (-ξ ^ 2 / 2)
    have he := hEnvelope c hc
    have hg : Integrable G := by
      exact (he.const_mul 2).add (by
        simpa only [neg_div, div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm] using
          integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
    have hh := tendsto_integral_of_dominated_convergence G
      (F := fun n ξ => min (((3 : ℝ) / (n + 1) * |ξ| ^ 3) *
        Real.exp (3 / (n + 1) * |ξ| ^ 3)) (G ξ)) (f := fun _ => 0)
      (fun n => by fun_prop) hg ?_ ?_
    · simpa [G] using hh
    · intro n
      exact Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by dsimp [G]; positivity))]
        exact min_le_right _ _
    · apply Filter.Eventually.of_forall
      intro ξ
      have hlim : Filter.Tendsto (fun n : ℕ => (3 : ℝ) / (n + 1) * |ξ| ^ 3)
          Filter.atTop (𝓝 0) := by
        have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3
        simpa only [mul_one_div, mul_zero, zero_mul] using hh.mul_const (|ξ| ^ 3)
      have hp := hlim.mul (Real.continuous_exp.continuousAt.tendsto.comp hlim)
      have hm := hp.min (tendsto_const_nhds (x := G ξ))
      have hG0 : 0 ≤ G ξ := by dsimp [G]; positivity
      simpa only [Real.exp_zero, zero_mul, min_eq_left hG0, Function.comp_def] using hm
  have hnoiseInversion (a : ℝ) (ν : ℝ≥0) (hν : ν ≠ 0) (h : ℝ) :
      (gaussianPDFReal a ν h : ℂ) =
        ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * ξ * h : ℝ) : ℂ) * Complex.I) *
          charFun (gaussianReal a ν) (-2 * Real.pi * ξ) := by
    clear * - a ν hν h
    have hv : 0 < (ν : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hν)
    have he (ξ : ℝ) :
        Complex.exp (((2 * Real.pi * ξ * h : ℝ) : ℂ) * Complex.I) *
          charFun (gaussianReal a ν) (-2 * Real.pi * ξ) =
        Complex.exp (Complex.I * ((2 * Real.pi * (h - a) : ℝ) : ℂ) * ξ) *
          Complex.exp (-((2 * Real.pi ^ 2 * (ν : ℝ) : ℝ) : ℂ) * ξ ^ 2) := by
      rw [charFun_gaussianReal, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [he]
    rw [fourierIntegral_gaussian (by
      simp only [Complex.ofReal_re]
      positivity)]
    rw [show (Real.pi : ℂ) / ((2 * Real.pi ^ 2 * (ν : ℝ) : ℝ) : ℂ) =
      (((2 * Real.pi * (ν : ℝ))⁻¹ : ℝ) : ℂ) by
        push_cast; field_simp [Complex.ofReal_ne_zero.mpr hv.ne', Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity : 0 ≤ (2 * Real.pi * (ν : ℝ))⁻¹),
      ← Real.sqrt_eq_rpow, Real.sqrt_inv]
    rw [show -(((2 * Real.pi * (h - a) : ℝ) : ℂ)) ^ 2 /
        (4 * ((2 * Real.pi ^ 2 * (ν : ℝ) : ℝ) : ℂ)) =
      ((-(h - a) ^ 2 / (2 * (ν : ℝ)) : ℝ) : ℂ) by
        push_cast; field_simp [Complex.ofReal_ne_zero.mpr hv.ne', Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring]
    simp only [gaussianPDFReal, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_exp]
  have hconvolutionInversion {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (E : Ω → ℝ) (hE : Measurable E) (a : ℝ)
      (ν : ℝ≥0) (hν : ν ≠ 0) (h : ℝ) :
      ((∫ z, gaussianPDFReal a ν (h - E z) ∂P : ℝ) : ℂ) =
        ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * ξ * h : ℝ) : ℂ) * Complex.I) *
          charFun (gaussianReal a ν) (-2 * Real.pi * ξ) *
          (∫ z, Complex.exp (((-2 * Real.pi * ξ * E z : ℝ) : ℂ) * Complex.I) ∂P) := by
    clear * - Ω P E hE a ν hν h hnoiseInversion
    let G : ℝ → ℝ := fun ξ => Real.exp (-(2 * Real.pi ^ 2 * (ν : ℝ)) * ξ ^ 2)
    let L : ℝ → Ω → ℂ := fun ξ z =>
      Complex.exp (((2 * Real.pi * ξ * (h - E z) : ℝ) : ℂ) * Complex.I) *
        charFun (gaussianReal a ν) (-2 * Real.pi * ξ)
    have hνp : 0 < (ν : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hν)
    have hg : Integrable G := integrable_exp_neg_mul_sq (by positivity)
    have hLn (ξ : ℝ) (z : Ω) : ‖L ξ z‖ = G ξ := by
      dsimp [L, G]
      rw [norm_mul, Complex.norm_exp, charFun_gaussianReal, Complex.norm_exp]
      have he : ((((2 * Real.pi * ξ * (h - E z) : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
      rw [he, Real.exp_zero, one_mul]
      congr 1
      simp only [sub_re, div_ofNat_re, mul_re, mul_im, ofReal_re, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero,
        mul_one, zero_add, pow_two]
      ring
    have hLi : Integrable (Function.uncurry L) (volume.prod P) := by
      apply (hg.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)).mono' (by dsimp [L]; fun_prop)
      exact Filter.Eventually.of_forall fun p => by
        change ‖L p.1 p.2‖ ≤ G p.1 * 1
        rw [mul_one]
        exact (hLn p.1 p.2).le
    rw [← integral_complex_ofReal]
    have he (z : Ω) : (gaussianPDFReal a ν (h - E z) : ℂ) =
        ∫ ξ : ℝ, L ξ z := by
      exact hnoiseInversion a ν hν (h - E z)
    simp_rw [he]
    rw [← integral_integral_swap hLi]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp only [L]
    rw [show 2 * Real.pi * ξ * (h - E z) =
      2 * Real.pi * ξ * h + (-2 * Real.pi * ξ * E z) by ring]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  have harrayLocal {I : Type u} [Fintype I] (a b : I → ℝ) (γ M ξ : ℝ)
      (hM : 0 ≤ M) (ha : ∀ j, |a j| ≤ M)
      (hsmall : 2 * |ξ| * M ≤ 1 / 2)
      (hv : 2 * (∑ j, a j ^ 2) + (∑ j, b j ^ 2) + γ ^ 2 = 1) :
      ‖Complex.exp (-((γ : ℂ) * ξ) ^ 2 / 2) *
        charFun ((Measure.pi (fun _ : I => gaussianReal 0 1)).map
          (fun z => ∑ j, (a j * (z j ^ 2 - 1) + b j * z j))) ξ -
        Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ ≤
        (3 * M * |ξ| ^ 3) * Real.exp (3 * M * |ξ| ^ 3) := by
    clear * - I a b γ M ξ hM ha hsmall hv hscalarLog hfiniteTransform
    let z : I → ℂ := fun j => 1 - 2 * (ξ : ℂ) * (a j : ℂ) * Complex.I
    let q : I → ℂ := fun j => ((ξ : ℂ) * (b j : ℂ)) ^ 2 / 2 -
      ((ξ : ℂ) * (b j : ℂ)) ^ 2 / (2 * z j)
    let r : I → ℂ := fun j => -(ξ : ℂ) * (a j : ℂ) * Complex.I -
      Complex.log (z j) / 2 + (ξ : ℂ) ^ 2 * (a j : ℂ) ^ 2 + q j
    have hq (j : I) : ‖q j‖ ≤ M * |ξ| ^ 3 * b j ^ 2 := by
      have hzre : (z j).re = 1 := by simp [z, mul_re, mul_im]
      have hzn : 1 ≤ ‖z j‖ := by simpa [hzre] using Complex.abs_re_le_norm (z j)
      have hz0 : z j ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hzn)
      have he : q j = (((ξ : ℂ) * (b j : ℂ)) ^ 2 / 2) * ((z j - 1) / z j) := by
        dsimp only [q]
        field_simp [hz0]
        <;> ring
      have hsub : ‖z j - 1‖ = 2 * |ξ| * |a j| := by
        rw [show z j - 1 = -2 * (ξ : ℂ) * (a j : ℂ) * Complex.I by dsimp [z]; ring]
        simp
      have hratio : ‖(z j - 1) / z j‖ ≤ 2 * |ξ| * M := by
        rw [norm_div, hsub]
        exact (div_le_self (by positivity) hzn).trans
          (mul_le_mul_of_nonneg_left (ha j) (by positivity))
      rw [he, norm_mul]
      have hn : ‖((ξ : ℂ) * (b j : ℂ)) ^ 2 / 2‖ = (|ξ| * |b j|) ^ 2 / 2 := by simp
      rw [hn]
      calc
        _ ≤ ((|ξ| * |b j|) ^ 2 / 2) * (2 * |ξ| * M) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by
          simp only [mul_pow, sq_abs]
          rw [← sq_abs ξ]
          ring
    have hr : ‖∑ j, r j‖ ≤ 3 * M * |ξ| ^ 3 := by
      have hsa : ∑ j, a j ^ 2 ≤ 1 / 2 := by
        nlinarith [sum_nonneg (s := univ) (fun j _ => sq_nonneg (b j)), sq_nonneg γ]
      have hsb : ∑ j, b j ^ 2 ≤ 1 := by
        nlinarith [sum_nonneg (s := univ) (fun j _ => sq_nonneg (a j)), sq_nonneg γ]
      calc
        _ ≤ ∑ j, ‖r j‖ := norm_sum_le _ _
        _ ≤ ∑ j, ((8 / 3 : ℝ) * |ξ| ^ 3 * M * a j ^ 2 + M * |ξ| ^ 3 * b j ^ 2) := by
          apply sum_le_sum
          intro j _
          refine (norm_add_le _ _).trans (add_le_add ?_ (hq j))
          let u : ℂ := -2 * (ξ : ℂ) * (a j : ℂ) * Complex.I
          have hu : ‖u‖ = 2 * |ξ| * |a j| := by simp [u]
          have hhalf : ‖u‖ ≤ 1 / 2 := by
            rw [hu]
            exact (mul_le_mul_of_nonneg_left (ha j) (by positivity)).trans hsmall
          have htaylor : logTaylor 3 u = u - u ^ 2 / 2 := by
            norm_num [logTaylor_succ, logTaylor_zero]
            ring
          have hid : -(ξ : ℂ) * (a j : ℂ) * Complex.I - log (z j) / 2 +
              (ξ : ℂ) ^ 2 * (a j : ℂ) ^ 2 = -(log (1 + u) - logTaylor 3 u) / 2 := by
            rw [htaylor]
            have hz : z j = 1 + u := by dsimp [z, u]; ring
            rw [hz]
            dsimp [u]
            ring_nf
            simp [Complex.I_sq]
          rw [hid, norm_div, norm_neg]
          norm_num only [norm_ofNat]
          have ht := Complex.norm_log_sub_logTaylor_le 2 (hhalf.trans_lt (by norm_num))
          norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at ht
          have hi : (1 - ‖u‖)⁻¹ ≤ 2 := by
            rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖u‖) (by norm_num : (0 : ℝ) < 2)]
            linarith
          calc
            _ ≤ (‖u‖ ^ 3 * (1 - ‖u‖)⁻¹ / 3) / 2 := by gcongr
            _ ≤ ‖u‖ ^ 3 / 3 := by nlinarith [mul_le_mul_of_nonneg_left hi (pow_nonneg (norm_nonneg u) 3)]
            _ = (8 / 3 : ℝ) * |ξ| ^ 3 * |a j| * a j ^ 2 := by rw [hu, ← sq_abs (a j)]; ring
            _ ≤ _ := by gcongr; exact ha j
        _ = (8 / 3 : ℝ) * |ξ| ^ 3 * M * (∑ j, a j ^ 2) +
            M * |ξ| ^ 3 * (∑ j, b j ^ 2) := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_left hsa (by positivity : 0 ≤ (8 / 3 : ℝ) * |ξ| ^ 3 * M),
            mul_le_mul_of_nonneg_left hsb (by positivity : 0 ≤ M * |ξ| ^ 3),
            mul_nonneg hM (pow_nonneg (abs_nonneg ξ) 3)]
    have he : Complex.exp (-((γ : ℂ) * ξ) ^ 2 / 2) *
        charFun ((Measure.pi (fun _ : I => gaussianReal 0 1)).map
          (fun z => ∑ j, (a j * (z j ^ 2 - 1) + b j * z j))) ξ =
        Complex.exp (-(ξ : ℂ) ^ 2 / 2) * Complex.exp (∑ j, r j) := by
      rw [hfiniteTransform]
      simp_rw [hscalarLog]
      have hp (j : I) : -(ξ : ℂ) * (a j : ℂ) * Complex.I -
          log (1 - 2 * (ξ : ℂ) * (a j : ℂ) * Complex.I) / 2 -
          ((ξ : ℂ) * (b j : ℂ)) ^ 2 / (2 * (1 - 2 * (ξ : ℂ) * (a j : ℂ) * Complex.I)) =
          r j - (ξ : ℂ) ^ 2 * (a j : ℂ) ^ 2 - (ξ : ℂ) ^ 2 * (b j : ℂ) ^ 2 / 2 := by
        dsimp only [r, q, z]
        ring
      simp_rw [hp]
      rw [← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [sum_sub_distrib, sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum]
      have hvC : 2 * (∑ j, (a j : ℂ) ^ 2) + (∑ j, (b j : ℂ) ^ 2) + (γ : ℂ) ^ 2 = 1 :=
        by exact_mod_cast hv
      linear_combination -((ξ : ℂ) ^ 2 / 2) * hvC
    rw [he, ← mul_sub_one, norm_mul]
    have hstd : ‖Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simp only [← ofReal_pow, ← ofReal_neg, ← ofReal_ofNat, ← ofReal_div, ofReal_re]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
    calc
      _ ≤ 1 * ‖Complex.exp (∑ j, r j) - 1‖ := mul_le_mul_of_nonneg_right hstd (norm_nonneg _)
      _ ≤ ‖∑ j, r j‖ * Real.exp ‖∑ j, r j‖ := by
        simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (∑ j, r j) 1
      _ ≤ _ := by gcongr
  have hglobal (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (n : ℕ) (hn : 7 ≤ n)
      (hMn : M ≤ 1 / ((n : ℝ) + 1)) (ψ : ℝ → ℂ)
      (henv : ∀ ξ, ‖ψ ξ‖ ≤ (1 + c * ξ ^ 2) ^ (-(8 : ℝ)))
      (hloc : ∀ ξ, 2 * |ξ| * M ≤ 1 / 2 →
        ‖ψ ξ - Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ ≤
          (3 * M * |ξ| ^ 3) * Real.exp (3 * M * |ξ| ^ 3)) (ξ : ℝ) :
      ‖ψ ξ - Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ ≤
        min (((3 : ℝ) / (n + 1) * |ξ| ^ 3) * Real.exp (3 / (n + 1) * |ξ| ^ 3))
          (2 * (1 + c * ξ ^ 2) ^ (-(8 : ℝ)) + Real.exp (-ξ ^ 2 / 2)) := by
    clear * - c M hc hM n hn hMn ψ henv hloc ξ
    let F : ℝ := (1 + c * ξ ^ 2) ^ (-(8 : ℝ))
    have hF1 : F ≤ 1 := by
      change (1 + c * ξ ^ 2) ^ (-(8 : ℝ)) ≤ 1
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · have hh : 0 ≤ c * ξ ^ 2 := by positivity
        linarith
      · norm_num
    have hgauss : ‖Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ = Real.exp (-ξ ^ 2 / 2) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hg1 : Real.exp (-ξ ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg ξ]
    have hG : ‖ψ ξ - Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ ≤ 2 * F + Real.exp (-ξ ^ 2 / 2) := by
      have hb := (norm_sub_le (ψ ξ) (Complex.exp (-(ξ : ℂ) ^ 2 / 2))).trans
        (add_le_add (henv ξ) (hgauss.le))
      have hF : 0 ≤ F := by positivity
      linarith
    apply le_min _ hG
    by_cases hcut : |ξ| ≤ ((n : ℝ) + 1) / 4
    · have hnpos : 0 < (n : ℝ) + 1 := by positivity
      have hs : 2 * |ξ| * M ≤ 1 / 2 := by
        calc
          _ ≤ 2 * (((n : ℝ) + 1) / 4) * (1 / ((n : ℝ) + 1)) := by gcongr
          _ = _ := by field_simp <;> ring
      have hcoef : 3 * M * |ξ| ^ 3 ≤ 3 / ((n : ℝ) + 1) * |ξ| ^ 3 := by
        simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMn (by norm_num)) (by positivity : 0 ≤ |ξ| ^ 3)
      exact (hloc ξ hs).trans
        (mul_le_mul hcoef (Real.exp_le_exp.mpr hcoef) (by positivity) (by positivity))
    · have hnreal : (7 : ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : 0 < (n : ℝ) + 1 := by positivity
      have hξ : ((n : ℝ) + 1) / 4 < |ξ| := lt_of_not_ge hcut
      have hcube : (((n : ℝ) + 1) / 4) ^ 3 ≤ |ξ| ^ 3 := by gcongr
      have hB : 3 ≤ (3 / ((n : ℝ) + 1) * |ξ| ^ 3) *
          Real.exp (3 / ((n : ℝ) + 1) * |ξ| ^ 3) := by
        have hbase : 3 ≤ 3 / ((n : ℝ) + 1) * |ξ| ^ 3 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]
          nlinarith [sq_nonneg ((n : ℝ) + 1), hcube]
        have hex : 1 ≤ Real.exp (3 / ((n : ℝ) + 1) * |ξ| ^ 3) :=
          Real.one_le_exp_iff.mpr (by positivity)
        nlinarith
      exact hG.trans ((by linarith : 2 * F + Real.exp (-ξ ^ 2 / 2) ≤ 3).trans hB)
  clear hbern hscalarLog hscalarNorm hnoiseInversion
  let L₀ : ℝ := κ ^ 3 / (2 * K ^ 2)
  let U₀ : ℝ := 1 + 2 * K ^ 2 / κ ^ 2 + 4 * K ^ 4 / κ ^ 3
  let M₀ : ℝ := K / (κ * Real.sqrt L₀)
  let A₀ : ℝ := κ ^ 2 / (4 * K ^ 2 * U₀)
  let cF : ℝ := A₀ * κ / 8
  let X₀ : ℝ := (R + κ⁻¹ ^ 2) / Real.sqrt L₀
  let η₀ : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-X₀ ^ 2 / 2)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL : 0 < L₀ := by dsimp [L₀]; positivity
  have hU : 0 < U₀ := by dsimp [U₀]; positivity
  have hM₀ : 0 < M₀ := by dsimp [M₀]; positivity
  have hA : 0 < A₀ := by dsimp [A₀]; positivity
  have hcF : 0 < cF := by dsimp [cF]; positivity
  have hη : 0 < η₀ :=
    mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)))
      (Real.exp_pos _)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, (∫ ξ : ℝ,
      min (((3 : ℝ) / (n + 1) * |ξ| ^ 3) * Real.exp (3 / (n + 1) * |ξ| ^ 3))
        (2 * (1 + cF * ξ ^ 2) ^ (-(8 : ℝ)) + Real.exp (-ξ ^ 2 / 2))) ≤ Real.pi * η₀ :=
    (herrorIntegral cF hcF).eventually (ge_mem_nhds (mul_pos Real.pi_pos hη))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let n : ℕ := max N 7
  have hn : 7 ≤ n := le_max_right _ _
  have hIn : (∫ ξ : ℝ,
      min (((3 : ℝ) / (n + 1) * |ξ| ^ 3) * Real.exp (3 / (n + 1) * |ξ| ^ 3))
        (2 * (1 + cF * ξ ^ 2) ^ (-(8 : ℝ)) + Real.exp (-ξ ^ 2 / 2))) ≤ Real.pi * η₀ :=
    hN n (le_max_left _ _)
  clear hevent hN herrorIntegral
  let δ₀ : ℝ := min (min 1 (κ / 32)) (1 / (M₀ ^ 2 * ((n : ℝ) + 1) ^ 2))
  let c : ℝ := η₀ / (2 * Real.sqrt U₀)
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  refine ⟨δ₀, c, hδ₀, (min_le_left _ _).trans (min_le_left _ _), by dsimp [c]; positivity, ?_⟩
  intro J _ _ H Core v e δ σ α t hδ hδsmall hσ hσ1 hα hv hvH
  dsimp only
  intro hVlo hVhi hvmax hCore hcard hcore hHcard he hd ht hsaddle homit
  clear hvH hVlo hHcard ht
  let V : ℝ := ∑ j, v j
  let d : J → ℝ := fun j => 1 - 2 * t * v j / α
  let ν : ℝ := δ * σ ^ 2 / α
  let P : Measure (H → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let w : J → ℝ := fun j => v j / (α * d j)
  let m : J → ℝ := fun j => -e j / d j
  let W : ℝ := 2 * (∑ j : H, w j ^ 2) + 4 * (∑ j : H, w j * m j ^ 2) + ν
  let τ : ℝ := ∑ j ∈ univ \ H, (w j + m j ^ 2)
  let μ : ℝ := (∑ j : H, (w j + m j ^ 2)) + ν * t
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα.1
  have hδ1 : δ ≤ 1 := hδsmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδcore : δ ≤ κ / 32 := hδsmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδM : δ ≤ 1 / (M₀ ^ 2 * ((n : ℝ) + 1) ^ 2) := hδsmall.trans (min_le_right _ _)
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hw0 (j : J) : 0 ≤ w j := div_nonneg (hv j) (mul_nonneg hαpos.le (hκ.le.trans (hd j).1))
  have hwupper (j : J) : w j ≤ v j / κ := by
    apply div_le_div_of_nonneg_left (hv j) hκ
    exact (hd j).1.trans (le_mul_of_one_le_left (hκ.le.trans (hd j).1) hα.1)
  have hwlower (j : J) (hj : j ∈ Core) : κ * δ / (2 * K) ≤ w j := by
    have hp : 0 < α * d j := mul_pos hαpos (hκ.trans_le (hd j).1)
    have hb : α * d j ≤ 2 * K :=
      mul_le_mul hα.2 (hd j).2 (hκ.le.trans (hd j).1) (by norm_num)
    exact (div_le_div_of_nonneg_left (mul_nonneg hκ.le hδ.le) hp hb).trans
      (div_le_div_of_nonneg_right (hcore j hj) hp.le)
  have hmupper (j : J) : m j ^ 2 ≤ K ^ 2 * v j * δ ^ 4 / κ ^ 2 := by
    have hesq : e j ^ 2 ≤ K ^ 2 * v j * δ ^ 4 := by
      have hh := sq_le_sq₀ (abs_nonneg (e j)) (by positivity) |>.mpr (he j)
      rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (hv j)] at hh
      simpa only [← pow_mul, show 2 * 2 = 4 by rfl] using hh
    dsimp [m]
    rw [div_pow, neg_sq]
    exact div_le_div₀
      (mul_nonneg (mul_nonneg (sq_nonneg K) (hv j)) (pow_nonneg hδ.le 4)) hesq (by positivity)
      (sq_le_sq₀ hκ.le (hκ.le.trans (hd j).1) |>.mpr (hd j).1)
  have hcenter : μ = V - τ := by
    clear * - μ V τ w m ν hsaddle H
    have hsplit := sum_sdiff (subset_univ H) (f := fun j => w j + m j ^ 2)
    have hsumH : (∑ j : H, (w j + m j ^ 2)) = ∑ j ∈ H, (w j + m j ^ 2) := by
      exact Finset.sum_coe_sort H (fun j : J => w j + m j ^ 2)
    dsimp only [μ, τ, V]
    rw [hsumH]
    have hs : (∑ j, (w j + m j ^ 2)) + ν * t = ∑ j, v j := by
      dsimp only [w, m, ν]
      simp only [sum_add_distrib, div_pow, neg_sq]
      calc
        _ = (∑ j, v j / (α * d j)) + (∑ j, e j ^ 2 / d j ^ 2) +
            δ * σ ^ 2 * t / α := by congr 1; ring
        _ = _ := hsaddle
    linarith
  have hτ : 0 ≤ τ ∧ τ ≤ κ⁻¹ ^ 2 * δ ^ 2 := by
    clear * - τ κ δ w m v e α d hα hκ hκ1 hd hv homit hw0
    constructor
    · exact sum_nonneg fun j hj => add_nonneg (hw0 j) (sq_nonneg _)
    · have hterm (j : J) : w j + m j ^ 2 ≤ κ⁻¹ ^ 2 * (v j + e j ^ 2) := by
        have hdpos : 0 < d j := hκ.trans_le (hd j).1
        dsimp [w, m]
        rw [div_pow, neg_sq]
        have hden1 : κ ^ 2 ≤ α * d j :=
          (show κ ^ 2 ≤ κ by nlinarith [hκ1]).trans
            ((hd j).1.trans (le_mul_of_one_le_left (hκ.le.trans (hd j).1) hα.1))
        have hden2 : κ ^ 2 ≤ d j ^ 2 := by nlinarith [(hd j).1]
        have hw := div_le_div_of_nonneg_left (hv j) (by positivity : 0 < κ ^ 2) hden1
        have hm := div_le_div_of_nonneg_left (sq_nonneg (e j)) (by positivity : 0 < κ ^ 2) hden2
        simpa [div_eq_mul_inv, inv_pow, mul_add, add_mul, mul_comm] using add_le_add hw hm
      exact (sum_le_sum (fun j hj => hterm j)).trans (by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left homit (by positivity))
  have hWbounds : L₀ * δ ≤ W ∧ W ≤ U₀ * δ := by
    clear * - L₀ U₀ W H Core v w m ν κ K δ hKpos hκ hδ hδ1 hα hαpos hσ hσ1 hcard hCore hw0 hwupper hwlower hmupper hVhi hv hvmax hν
    have hsumv : (∑ j : H, v j) ≤ K := by
      rw [Finset.sum_coe_sort]
      exact (sum_le_sum_of_subset_of_nonneg (subset_univ H)
        (fun j _ _ => hv j)).trans hVhi
    have hcoreSum : (Core.card : ℝ) * (κ * δ / (2 * K)) ^ 2 ≤
        ∑ j : H, w j ^ 2 := by
      rw [Finset.sum_coe_sort H (fun j : J => w j ^ 2)]
      calc
        _ = ∑ _j ∈ Core, (κ * δ / (2 * K)) ^ 2 := by simp
        _ ≤ ∑ j ∈ Core, w j ^ 2 := sum_le_sum fun j hj =>
          (sq_le_sq₀ (by positivity) (hw0 j)).mpr (hwlower j hj)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hCore (fun j _ _ => sq_nonneg _)
    have hlow : L₀ * δ ≤ 2 * (∑ j : H, w j ^ 2) := by
      have hh := mul_le_mul_of_nonneg_right hcard
        (sq_nonneg (κ * δ / (2 * K)))
      have hid : 2 * (κ / δ * (κ * δ / (2 * K)) ^ 2) = L₀ * δ := by
        dsimp [L₀]
        field_simp <;> ring
      rw [← hid]
      exact mul_le_mul_of_nonneg_left (hh.trans hcoreSum) (by norm_num)
    have henergy : 2 * (∑ j : H, w j ^ 2) + 4 * (∑ j : H, w j * m j ^ 2) ≤
        (2 * K ^ 2 / κ ^ 2 + 4 * K ^ 4 / κ ^ 3) * δ := by
      have hδfour : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
      have hterm (j : H) : 2 * w j ^ 2 + 4 * (w j * m j ^ 2) ≤
          (2 * K * δ / κ ^ 2 + 4 * K ^ 3 * δ / κ ^ 3) * v j := by
        have hwmax := (hwupper j).trans (div_le_div_of_nonneg_right (hvmax j) hκ.le)
        have hs : w j ^ 2 ≤ (K * δ / κ ^ 2) * v j := by
          calc
            _ ≤ (v j / κ) * (K * δ / κ) := by
              rw [pow_two]
              exact mul_le_mul (hwupper j) hwmax (hw0 j) (div_nonneg (hv j) hκ.le)
            _ = _ := by ring
        have hm : m j ^ 2 ≤ K ^ 2 * v j / κ ^ 2 := by
          calc
            _ ≤ (K ^ 2 * v j / κ ^ 2) * δ ^ 4 := (hmupper j).trans_eq (by ring)
            _ ≤ (K ^ 2 * v j / κ ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left hδfour (div_nonneg (mul_nonneg (sq_nonneg K) (hv j)) (sq_nonneg κ))
            _ = _ := mul_one _
        have hc : w j * m j ^ 2 ≤ (K ^ 3 * δ / κ ^ 3) * v j :=
          (mul_le_mul hwmax hm (sq_nonneg (m j)) (by positivity)).trans_eq (by ring)
        exact (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4))).trans_eq (by ring)
      calc
        _ = ∑ j : H, (2 * w j ^ 2 + 4 * (w j * m j ^ 2)) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ ∑ j : H, (2 * K * δ / κ ^ 2 + 4 * K ^ 3 * δ / κ ^ 3) * v j :=
          sum_le_sum fun j _ => hterm j
        _ = (2 * K * δ / κ ^ 2 + 4 * K ^ 3 * δ / κ ^ 3) * ∑ j : H, v j :=
          (mul_sum _ _ _).symm
        _ ≤ (2 * K * δ / κ ^ 2 + 4 * K ^ 3 * δ / κ ^ 3) * K :=
          mul_le_mul_of_nonneg_left hsumv (by positivity)
        _ = _ := by ring
    have hνupper : ν ≤ δ := by
      dsimp [ν]
      apply (div_le_iff₀ hαpos).mpr
      calc
        δ * σ ^ 2 ≤ δ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hσ.le hσ1) hδ.le
        _ = δ := mul_one δ
        _ ≤ δ * α := le_mul_of_one_le_right hδ.le hα.1
    constructor
    · exact hlow.trans (by
        dsimp only [W]
        linarith only [hν, sum_nonneg (s := univ) (fun (j : H) _ => mul_nonneg (hw0 j) (sq_nonneg (m j)))])
    · change 2 * (∑ j : H, w j ^ 2) + 4 * (∑ j : H, w j * m j ^ 2) + ν ≤
        (1 + 2 * K ^ 2 / κ ^ 2 + 4 * K ^ 4 / κ ^ 3) * δ
      calc
        _ ≤ (2 * K ^ 2 / κ ^ 2 + 4 * K ^ 4 / κ ^ 3) * δ + δ := add_le_add henergy hνupper
        _ = _ := by ring
  have hW : 0 < W := (mul_pos hL hδ).trans_le hWbounds.1
  have hwdef : w = fun j => v j / (α * d j) := rfl
  have hmdef : m = fun j => -e j / d j := rfl
  have hνdef : ν = δ * σ ^ 2 / α := rfl
  clear_value w m ν
  let a : H → ℝ := fun j => w j / Real.sqrt W
  let b : H → ℝ := fun j => 2 * m j * Real.sqrt (w j) / Real.sqrt W
  let γ : ℝ := Real.sqrt ν / Real.sqrt W
  let M : ℝ := M₀ * Real.sqrt δ
  let CoreH : Finset H := univ.filter fun j => (j : J) ∈ Core
  let Q : (H → ℝ) → ℝ := fun z => ∑ j, (a j * (z j ^ 2 - 1) + b j * z j)
  let ψ : ℝ → ℂ := fun ξ => Complex.exp (-((γ : ℂ) * ξ) ^ 2 / 2) * charFun (P.map Q) ξ
  have hvariance : 2 * (∑ j, a j ^ 2) + (∑ j, b j ^ 2) + γ ^ 2 = 1 := by
    clear * - a b γ W ν w m hν hW hw0
    dsimp only [a, b, γ]
    simp only [div_pow, mul_pow, Real.sq_sqrt hν.le, Real.sq_sqrt hW.le,
      Real.sq_sqrt (hw0 _), ← sum_div]
    field_simp
    simp only [show (2 : ℝ) ^ 2 = 4 by norm_num, mul_assoc]
    rw [← mul_sum]
    dsimp only [W]
    congr 2
    congr 1
    apply sum_congr rfl
    intro j hj
    ring
  clear_value W
  have ha : ∀ j, |a j| ≤ M := by
    clear * - a M M₀ L₀ δ W K κ hδ hκ hL hW hw0 hwupper hvmax hWbounds hKpos
    intro j
    have hw := (hwupper j).trans (div_le_div_of_nonneg_right (hvmax j) hκ.le)
    have hs : Real.sqrt (L₀ * δ) ≤ Real.sqrt W := Real.sqrt_le_sqrt hWbounds.1
    rw [Real.sqrt_mul hL.le] at hs
    dsimp only [a, M, M₀]
    rw [abs_of_nonneg (div_nonneg (hw0 j) (Real.sqrt_nonneg W))]
    have hh := div_le_div₀ (by positivity : 0 ≤ K * δ / κ) hw
      (mul_pos (Real.sqrt_pos.mpr hL) (Real.sqrt_pos.mpr hδ)) hs
    calc
      _ ≤ (K * δ / κ) / (Real.sqrt L₀ * Real.sqrt δ) := hh
      _ = _ := by
        field_simp [hκ.ne', (Real.sqrt_pos.mpr hL).ne', (Real.sqrt_pos.mpr hδ).ne']
        nlinarith [Real.sq_sqrt hδ.le]
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMn : M ≤ 1 / ((n : ℝ) + 1) := by
    clear * - M M₀ δ n hδ hδM hM₀
    dsimp [M]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, Real.sq_sqrt hδ.le, div_pow, one_pow]
    exact (mul_le_mul_of_nonneg_left hδM (sq_nonneg M₀)).trans_eq (by field_simp)
  have hcoreH : κ / δ ≤ (CoreH.card : ℝ) ∧ ∀ j ∈ CoreH, A₀ * δ ≤ a j ^ 2 := by
    clear * - CoreH Core H κ δ A₀ a U₀ W w K hcard hCore hwlower hw0 hW hWbounds hδ hKpos hU hκ
    constructor
    · convert hcard using 1
      have hbij : CoreH.card = Core.card := by
        have heq : CoreH = Core.subtype (· ∈ H) := by ext j; simp [CoreH]
        rw [heq, Finset.card_subtype, Finset.filter_eq_self.mpr (fun j hj => hCore hj)]
      exact_mod_cast hbij
    · intro j hj
      have hjC : (j : J) ∈ Core := (mem_filter.mp hj).2
      have hw := hwlower j hjC
      have hWu := hWbounds.2
      dsimp only [a, A₀]
      rw [div_pow, Real.sq_sqrt hW.le]
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ κ * δ / (2 * K))
        (hw0 j)).mpr hw
      have hh := div_le_div₀ (sq_nonneg (w j)) hsq hW hWu
      have hid : κ ^ 2 / (4 * K ^ 2 * U₀) * δ =
          (κ * δ / (2 * K)) ^ 2 / (U₀ * δ) := by
        field_simp <;> ring
      rw [hid]
      exact hh
  have henv (ξ : ℝ) : ‖ψ ξ‖ ≤ (1 + cF * ξ ^ 2) ^ (-(8 : ℝ)) := by
    dsimp only [ψ, Q, P]
    rw [hfiniteTransform]
    have hc : A₀ * κ * ξ ^ 2 / 8 = cF * ξ ^ 2 := by dsimp only [cF]; ring
    simpa only [hc] using harrayEnvelope a b γ δ A₀ κ CoreH hδ hA hκ
      hδcore hcoreH.1 hcoreH.2 ξ
  have hloc (ξ : ℝ) (hs : 2 * |ξ| * M ≤ 1 / 2) :
      ‖ψ ξ - Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ ≤
        (3 * M * |ξ| ^ 3) * Real.exp (3 * M * |ξ| ^ 3) :=
    harrayLocal a b γ M ξ hM ha hs hvariance
  have herror (ξ : ℝ) : ‖ψ ξ - Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ ≤
      min (((3 : ℝ) / (n + 1) * |ξ| ^ 3) * Real.exp (3 / (n + 1) * |ξ| ^ 3))
        (2 * (1 + cF * ξ ^ 2) ^ (-(8 : ℝ)) + Real.exp (-ξ ^ 2 / 2)) :=
    hglobal cF M hcF hM n hn hMn ψ henv hloc ξ
  have hψ : Continuous ψ := by
    dsimp only [ψ]
    exact (by fun_prop : Continuous (fun ξ : ℝ => Complex.exp (-((γ : ℂ) * ξ) ^ 2 / 2))).mul
      (continuous_charFun (μ := P.map Q))
  clear harrayEnvelope hfiniteTransform harrayLocal hglobal hloc hvariance ha hM hMn hcoreH
  intro y hy
  let h : ℝ := V + Real.sqrt δ * y
  let E : (H → ℝ) → ℝ := fun z => ∑ j : H, (Real.sqrt (w j) * z j + m j) ^ 2
  let gt : ℝ := ∫ z, gaussianPDFReal (ν * t) ν.toNNReal (h - E z) ∂P
  let x : ℝ := (h - μ) / Real.sqrt W
  have hstandard (z : H → ℝ) : (E z - ∑ j : H, (w j + m j ^ 2)) / Real.sqrt W = Q z := by
    clear * - E Q a b W w m hw0
    dsimp only [E, Q, a, b]
    rw [← sum_sub_distrib, sum_div]
    apply sum_congr rfl
    intro j hj
    rw [add_sq, mul_pow, Real.sq_sqrt (hw0 j)]
    ring
  have hEm : Measurable E := by dsimp [E]; fun_prop
  have hQm : Measurable Q := by dsimp [Q]; fun_prop
  have hγ : γ ^ 2 = ν / W := by
    dsimp only [γ]
    rw [div_pow, Real.sq_sqrt hν.le, Real.sq_sqrt hW.le]
  clear_value Q a b γ
  clear hmupper hwupper hwlower hvmax hδM hδcore he hd hcore hcard hCore
  have hinv : (gt : ℂ) = ∫ ξ : ℝ,
      Complex.exp (((2 * Real.pi * ξ * h : ℝ) : ℂ) * Complex.I) *
        charFun (gaussianReal (ν * t) ν.toNNReal) (-2 * Real.pi * ξ) *
        (∫ z, Complex.exp (((-2 * Real.pi * ξ * E z : ℝ) : ℂ) * Complex.I) ∂P) :=
    hconvolutionInversion P E hEm (ν * t) ν.toNNReal (ne_of_gt (Real.toNNReal_pos.mpr hν)) h
  clear hconvolutionInversion hEm
  have hdensity : ((Real.sqrt W * gt : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) *
      ∫ ξ : ℝ, Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I) * ψ ξ := by
    clear * - W gt x h μ ν t P Q γ E hW hν hinv hstandard hQm hγ
    let C : ℝ := ∑ j : H, (w j + m j ^ 2)
    let s : ℝ := Real.sqrt W
    have hs : 0 < s := Real.sqrt_pos.mpr hW
    have hs2 : s ^ 2 = W := Real.sq_sqrt hW.le
    let f : ℝ → ℂ := fun ξ =>
        Complex.exp (((2 * Real.pi * ξ * h : ℝ) : ℂ) * Complex.I) *
          charFun (gaussianReal (ν * t) ν.toNNReal) (-2 * Real.pi * ξ) *
          (∫ z, Complex.exp (((-2 * Real.pi * ξ * E z : ℝ) : ℂ) * Complex.I) ∂P)
    have hf (ξ : ℝ) : f (ξ / (-(2 * Real.pi * s))) =
        Complex.exp (-(ξ : ℂ) * (((h - (C + ν * t)) / s : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (-((γ : ℂ) * ξ) ^ 2 / 2) * charFun (P.map Q) ξ) := by
      dsimp only [f]
      rw [charFun_gaussianReal, Real.coe_toNNReal ν hν.le,
        charFun_apply_real, integral_map hQm.aemeasurable (by fun_prop)]
      simp only [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      simp only [← Complex.exp_add]
      congr 1
      have he : E z = s * Q z + C := by
        have hz := hstandard z
        change (E z - C) / s = Q z at hz
        rw [div_eq_iff hs.ne'] at hz
        linarith
      rw [he]
      have hγeq : γ ^ 2 * s ^ 2 = ν := by rw [hs2, hγ]; field_simp
      have hγC : (γ : ℂ) ^ 2 * (s : ℂ) ^ 2 = (ν : ℂ) := by exact_mod_cast hγeq
      have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
      have hγdiv : (γ : ℂ) ^ 2 = (ν : ℂ) / (s : ℂ) ^ 2 :=
        (eq_div_iff (pow_ne_zero 2 hsC)).2 hγC
      push_cast
      simp only [mul_pow, hγdiv]
      field_simp [hsC, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
    have hsub := Measure.integral_comp_div f (-(2 * Real.pi * s))
    rw [abs_neg, abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hs),
      Complex.real_smul] at hsub
    have hint : (∫ ξ : ℝ, f (ξ / (-(2 * Real.pi * s)))) =
        (2 * Real.pi * s : ℝ) * (gt : ℂ) := by
      rw [hsub]
      change (2 * Real.pi * s : ℝ) * (∫ ξ : ℝ, f ξ) = _
      rw [← hinv]
    rw [show ((Real.sqrt W * gt : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) *
        ((2 * Real.pi * s : ℝ) * (gt : ℂ)) by
          dsimp only [s]; push_cast; field_simp <;> ring]
    rw [← hint]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hf)
  have hgauss : ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ,
        Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I) * Complex.exp (-(ξ : ℂ) ^ 2 / 2) := by
    clear_value x
    clear * - x
    simp_rw [show ∀ ξ : ℝ, -(ξ : ℂ) * (x : ℂ) * Complex.I =
      (-x : ℂ) * ξ * Complex.I from fun ξ => by ring]
    have hg := StatLean.HypothesisTesting.integral_cexp_mul_gaussian (-x)
    simp only [Complex.ofReal_neg, neg_sq] at hg
    rw [hg]
    push_cast
    rw [← mul_assoc]
    congr 1
    norm_cast
    rw [one_div, ← div_eq_inv_mul, Real.sqrt_div_self]
  clear_value ψ
  clear hQm hinv hstandard
  have hLone : |Real.sqrt W * gt - (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)| ≤ η₀ / 2 := by
    clear_value x gt η₀
    clear * - W gt x η₀ ψ cF n hcF hEnvelope henv herror hIn hdensity hgauss hψ
    let phase : ℝ → ℂ := fun ξ => Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I)
    let F : ℝ → ℂ := fun ξ => phase ξ * ψ ξ
    let G : ℝ → ℂ := fun ξ => phase ξ * Complex.exp (-(ξ : ℂ) ^ 2 / 2)
    let B : ℝ → ℝ := fun ξ =>
      min (((3 : ℝ) / (n + 1) * |ξ| ^ 3) * Real.exp (3 / (n + 1) * |ξ| ^ 3))
        (2 * (1 + cF * ξ ^ 2) ^ (-(8 : ℝ)) + Real.exp (-ξ ^ 2 / 2))
    have hp (ξ : ℝ) : ‖phase ξ‖ = 1 := by
      simpa only [phase, ← ofReal_neg, ← ofReal_mul] using
        Complex.norm_exp_ofReal_mul_I (-ξ * x)
    have hg (ξ : ℝ) : ‖Complex.exp (-(ξ : ℂ) ^ 2 / 2)‖ = Real.exp (-ξ ^ 2 / 2) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hei := hEnvelope cF hcF
    have hgi : Integrable (fun ξ : ℝ => Real.exp (-ξ ^ 2 / 2)) := by
      simpa only [neg_div, div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm] using
        integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    have hFm : AEStronglyMeasurable F := by
      dsimp only [F]
      exact (by fun_prop : Continuous phase).aestronglyMeasurable.mul hψ.aestronglyMeasurable
    have hFi : Integrable F := hei.mono' hFm (Filter.Eventually.of_forall fun ξ => by
      dsimp only [F]
      rw [norm_mul, hp, one_mul]
      exact henv ξ)
    have hGi : Integrable G := hgi.mono' (by dsimp only [G, phase]; fun_prop)
      (Filter.Eventually.of_forall fun ξ => by dsimp only [G]; rw [norm_mul, hp, one_mul, hg])
    have hBi : Integrable B := ((hei.const_mul 2).add hgi).mono' (by dsimp only [B]; fun_prop)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [B]; positivity)]
        exact min_le_right _ _)
    have hpoint (ξ : ℝ) : ‖F ξ - G ξ‖ ≤ B ξ := by
      dsimp only [F, G]
      rw [← mul_sub, norm_mul, hp, one_mul]
      exact herror ξ
    have hid : ((Real.sqrt W * gt - (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) =
        (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, (F ξ - G ξ) := by
      push_cast at hdensity hgauss ⊢
      rw [hdensity, hgauss, integral_sub hFi hGi]
      ring
    have hk : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hid, norm_mul, hk]
    calc
      _ ≤ (1 / (2 * Real.pi)) * ∫ ξ : ℝ, ‖F ξ - G ξ‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ ≤ (1 / (2 * Real.pi)) * ∫ ξ : ℝ, B ξ :=
        mul_le_mul_of_nonneg_left (integral_mono (hFi.sub hGi).norm hBi hpoint) (by positivity)
      _ ≤ (1 / (2 * Real.pi)) * (Real.pi * η₀) :=
        mul_le_mul_of_nonneg_left hIn (by positivity)
      _ = _ := by field_simp <;> ring
  have hx : |x| ≤ X₀ := by
    clear * - x X₀ L₀ δ W κ R τ h μ hWbounds hcenter hτ hδ hδ1 hL hR hy
    have hs := Real.sqrt_le_sqrt hWbounds.1
    rw [Real.sqrt_mul hL.le] at hs
    have hτsmall : τ ≤ κ⁻¹ ^ 2 * Real.sqrt δ := by
      have hd : δ ^ 2 ≤ Real.sqrt δ := by
        calc
          δ ^ 2 = δ * δ := pow_two _
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1 hδ.le
          _ = δ := mul_one _
          _ ≤ Real.sqrt δ := Real.le_sqrt_self_iff.mpr hδ1
      exact hτ.2.trans (mul_le_mul_of_nonneg_left hd (by positivity))
    have hnum : |h - μ| ≤ Real.sqrt δ * (R + κ⁻¹ ^ 2) := by
      have heq : h - μ = Real.sqrt δ * y + τ := by
        rw [hcenter]
        dsimp only [h]
        ring
      rw [heq]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hτ.1]
        nlinarith [mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg δ)])
    dsimp only [x]
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg W)]
    have hh := div_le_div₀
      (mul_nonneg (Real.sqrt_nonneg δ) (add_nonneg hR (sq_nonneg _)))
      hnum (mul_pos (Real.sqrt_pos.mpr hL) (Real.sqrt_pos.mpr hδ)) hs
    calc
      _ ≤ (Real.sqrt δ * (R + κ⁻¹ ^ 2)) /
          (Real.sqrt L₀ * Real.sqrt δ) := hh
      _ = X₀ := by
        dsimp only [X₀]
        field_simp [(Real.sqrt_pos.mpr hδ).ne', (Real.sqrt_pos.mpr hL).ne']
        <;> ring
  have hphi : η₀ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    clear * - η₀ x X₀ hx
    dsimp only [η₀]
    clear_value x X₀
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ X₀ := le_trans (abs_nonneg x) hx
    have hh := sq_le_sq₀ (abs_nonneg x) hx0 |>.mpr hx
    rw [sq_abs] at hh
    linarith
  have hscaled : η₀ / 2 ≤ Real.sqrt W * gt := by
    clear * - η₀ W gt x hLone hphi
    clear_value gt x η₀
    have hh := (abs_le.mp hLone).1
    linarith
  have hsqrt : Real.sqrt W ≤ Real.sqrt U₀ * Real.sqrt δ := by
    clear * - W U₀ δ hU hWbounds
    clear_value U₀
    rw [← Real.sqrt_mul hU.le]
    exact Real.sqrt_le_sqrt hWbounds.2
  have hgt : c / Real.sqrt δ ≤ gt := by
    clear * - c U₀ δ W gt η₀ hU hδ hW hscaled hsqrt
    dsimp only [c]
    have hgt0 : 0 ≤ gt :=
      integral_nonneg fun z => gaussianPDFReal_nonneg (ν * t) ν.toNNReal (h - E z)
    clear_value U₀ gt η₀
    have hh := mul_le_mul_of_nonneg_right hsqrt hgt0
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hδ)).mpr
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt U₀)).mpr
    nlinarith
  clear * - hgt gt h E hwdef hmdef hνdef P V d
  simpa only [gt, h, E, hwdef, hmdef, hνdef, P, V, d, sub_eq_add_neg, neg_div] using hgt

#print axioms result
end D5.S3.Fourier.Asymptotics.GaussianQuadraticTiltedDensity
