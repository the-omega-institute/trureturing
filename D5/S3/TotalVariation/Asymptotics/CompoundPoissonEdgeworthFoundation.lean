/- GID: D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite signed smoothing and low-frequency Gaussian error decay for two-jump Poisson laws. -/

import D5.S3.TotalVariation.Asymptotics.StatLeanFourierSuppliers
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory ProbabilityTheory Set Filter Convolution
open scoped FourierTransform Real NNReal ENNReal Topology BigOperators
noncomputable section
namespace CompoundPoissonEdgeworth
open StatLean.HypothesisTesting hiding edgeworthCDF

def pairLaw (p q : ℝ≥0) (a b : ℝ) : Measure ℝ :=
  ((poissonMeasure p).prod (poissonMeasure q)).map
    (fun n : ℕ × ℕ => a*(n.1:ℝ)+b*(n.2:ℝ))

def damping (p q a b t : ℝ) : ℝ := p*(1-Real.cos (t*a))+q*(1-Real.cos (t*b))

def centeredExponent (lam p q a b t : ℝ) : ℂ :=
  (lam:ℂ)*((p:ℂ)*(Complex.exp ((t*a:ℝ)*Complex.I)-1-(t*a:ℝ)*Complex.I)+
    (q:ℂ)*(Complex.exp ((t*b:ℝ)*Complex.I)-1-(t*b:ℝ)*Complex.I))

def centeredLaw (lam p q a b : ℝ) : Measure ℝ :=
  (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b).map
    (fun z => z-lam*(p*a+q*b))

def smoothingLaw (k : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (k y))

def smoothedSignedDensity (k q : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, k y * q (x-y)

def fejerDensity (B x : ℝ) : ℝ :=
  B * (Real.sin (Real.pi*(B*x))/(Real.pi*(B*x)))^2

/-- Finite signed smoothing with a universal Fejer tail constant. -/
theorem generic_finite_smoothing :
      ∃ H : ℝ, 0 < H ∧
        ∀ (P : Measure ℝ) [IsProbabilityMeasure P] (q : ℝ → ℝ),
        Integrable q → ∀ A : ℝ≥0, (∀ x, |q x| ≤ A) →
        LipschitzWith A (densityCDF q) →
        ∀ B : ℝ, 0 < B →
        IntegrableOn (fun ξ : ℝ =>
          ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
            (Real.pi*|ξ|)) (Icc (-B) B) →
        ∀ x : ℝ, |P.real (Iic x)-densityCDF q x| ≤
          2*(∫ ξ in Icc (-B) B,
            ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
              (Real.pi*|ξ|)) + 4*(A:ℝ)*H/B := by
  have signed_smoothing_absorption
      (F G : ℝ → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (hF : Monotone F) (A : ℝ≥0) (hG : LipschitzWith A G)
      (hbounded : BddAbove (Set.range (fun x => |F x - G x|)))
      (h D : ℝ) (hh : 0 ≤ h)
      (htail : ν.real {y : ℝ | h < |y|} < 1/2)
      (hconv : ∀ x : ℝ, |∫ y, (F (x-y)-G (x-y)) ∂ν| ≤ D) :
      ∀ x : ℝ, |F x-G x| ≤
        (D + 2*(A:ℝ)*h)/(1-2*ν.real {y : ℝ | h < |y|}) := by
    let H := fun x => F x-G x
    let B := sSup (Set.range (fun x => |H x|))
    let S := {y : ℝ | h < |y|}
    have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
    have hB (x : ℝ) : |H x| ≤ B := le_csSup hbounded ⟨x,rfl⟩
    have hB0 : 0 ≤ B := (abs_nonneg (H 0)).trans (hB 0)
    have hmeas : Measurable H := hF.measurable.sub hG.continuous.measurable
    have hint (x : ℝ) : Integrable (fun y => H (x-y)) ν := by
      apply Integrable.mono' (integrable_const B)
        (hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun y => by
        change ‖H (x-y)‖ ≤ B
        rw [Real.norm_eq_abs]
        exact hB (x-y)
    have htailint : Integrable (S.indicator (fun _ : ℝ => 2*B)) ν :=
      (integrable_const (2*B)).indicator hS
    have htailval : (∫ y, S.indicator (fun _ : ℝ => 2*B) y ∂ν) = 2*B*ν.real S := by
      rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]
    have hA : 0 ≤ (A:ℝ) := A.property
    have hgood (x y : ℝ) (hy : y ∉ S) :
        H x ≤ H (x+h-y) + 2*(A:ℝ)*h ∧
        -H x ≤ -H (x-h-y) + 2*(A:ℝ)*h := by
      have hy' : |y| ≤ h := le_of_not_gt hy
      have hylo := (abs_le.mp hy').1
      have hyhi := (abs_le.mp hy').2
      have hfup := hF (show x ≤ x+h-y by linarith)
      have hfdn := hF (show x-h-y ≤ x by linarith)
      have hgup := hG.dist_le_mul (x+h-y) x
      have hgdn := hG.dist_le_mul (x-h-y) x
      rw [Real.dist_eq, Real.dist_eq] at hgup hgdn
      have hupdist : |x+h-y-x| ≤ 2*h := abs_le.mpr ⟨by linarith, by linarith⟩
      have hdndist : |x-h-y-x| ≤ 2*h := abs_le.mpr ⟨by linarith, by linarith⟩
      have hup := hgup.trans (mul_le_mul_of_nonneg_left hupdist hA)
      have hdn := hgdn.trans (mul_le_mul_of_nonneg_left hdndist hA)
      dsimp [H]
      constructor
      · have := (abs_le.mp hup).2
        linarith only [hfup,this]
      · have := (abs_le.mp hdn).1
        linarith only [hfdn,this]
    have hpoint (x y : ℝ) :
        H x ≤ H (x+h-y) + 2*(A:ℝ)*h + S.indicator (fun _ => 2*B) y ∧
        -H x ≤ -H (x-h-y) + 2*(A:ℝ)*h + S.indicator (fun _ => 2*B) y := by
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        have hb0 := abs_le.mp (hB x)
        have hb1 := abs_le.mp (hB (x+h-y))
        have hb2 := abs_le.mp (hB (x-h-y))
        have hnn : 0 ≤ 2*(A:ℝ)*h := by positivity
        constructor <;> linarith only [hb0.1,hb0.2,hb1.1,hb1.2,hb2.1,hb2.2,hnn]
      · simpa only [Set.indicator_of_notMem hy, add_zero] using hgood x y hy
    have hbound (x : ℝ) : |H x| ≤ D+2*(A:ℝ)*h+2*B*ν.real S := by
      have hup := integral_mono (μ:=ν) (integrable_const (H x))
        (((hint (x+h)).add (integrable_const (2*(A:ℝ)*h))).add htailint) (fun y => (hpoint x y).1)
      have hdn := integral_mono (μ:=ν) (integrable_const (-H x))
        (((hint (x-h)).neg.add (integrable_const (2*(A:ℝ)*h))).add htailint) (fun y => (hpoint x y).2)
      simp only [Pi.add_apply, Pi.neg_apply] at hup hdn
      rw [integral_add (f := fun y => H (x+h-y)+2*(A:ℝ)*h) ((hint (x+h)).add (integrable_const (2*(A:ℝ)*h))) htailint,
        integral_add (hint (x+h)) (integrable_const (2*(A:ℝ)*h)), htailval] at hup
      rw [integral_add (f := fun y => -H (x-h-y)+2*(A:ℝ)*h) ((hint (x-h)).neg.add (integrable_const (2*(A:ℝ)*h))) htailint,
        integral_add (f := fun y => -H (x-h-y)) (hint (x-h)).neg (integrable_const (2*(A:ℝ)*h)), integral_neg, htailval] at hdn
      simp only [integral_const, probReal_univ, one_smul] at hup hdn
      rw [integral_neg] at hdn
      dsimp only [H] at hup hdn
      have hc1 := (abs_le.mp (hconv (x+h))).2
      have hc2 := (abs_le.mp (hconv (x-h))).1
      change _ ≤ D at hc1
      change -D ≤ _ at hc2
      exact abs_le.mpr ⟨by linarith only [hdn,hc2], by linarith only [hup,hc1]⟩
    have hsup : B ≤ D+2*(A:ℝ)*h+2*B*ν.real S :=
      csSup_le (Set.range_nonempty _) (by rintro z ⟨x,rfl⟩; exact hbound x)
    have hden : 0 < 1-2*ν.real S := by dsimp [S]; linarith only [htail]
    have hfinal : B ≤ (D+2*(A:ℝ)*h)/(1-2*ν.real S) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [hsup]
    exact fun x => (hB x).trans hfinal

  have signed_convolution_bridge (k q : ℝ → ℝ)
      (hk : Integrable k) (hq : Integrable q) (hk0 : ∀ y, 0 ≤ k y) :
      Integrable (smoothedSignedDensity k q) ∧
      (∀ x, densityCDF (smoothedSignedDensity k q) x =
        ∫ y, densityCDF q (x-y) ∂smoothingLaw k) ∧
      (∀ t, charFunDensity (smoothedSignedDensity k q) t =
        charFun (smoothingLaw k) t * charFunDensity q t) := by
    have hprod : Integrable (fun p : ℝ × ℝ => k p.2 * q (p.1-p.2))
        (volume.prod volume) := hk.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hq
    have hsmooth : Integrable (smoothedSignedDensity k q) := hprod.integral_prod_left
    have hwith (f : ℝ → ℝ) : (∫ y, f y ∂smoothingLaw k) = ∫ y, k y * f y := by
      rw [smoothingLaw, integral_withDensity_eq_integral_toReal_smul₀
        hk.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
      simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul]
    have hwithC (f : ℝ → ℂ) : (∫ y, f y ∂smoothingLaw k) = ∫ y, (k y : ℂ) * f y := by
      rw [smoothingLaw, integral_withDensity_eq_integral_toReal_smul₀
        hk.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
      simp only [ENNReal.toReal_ofReal (hk0 _), Complex.real_smul]
    refine ⟨hsmooth, ?_, ?_⟩
    · intro x
      rw [hwith, densityCDF, ← integral_indicator measurableSet_Iic]
      have hprodI := hprod.indicator
        (measurableSet_Iic.preimage measurable_fst : MeasurableSet {p : ℝ × ℝ | p.1 ≤ x})
      have hswap :
          (∫ z, ∫ y, (Iic x).indicator (fun z => k y * q (z-y)) z) =
          ∫ y, ∫ z, (Iic x).indicator (fun z => k y * q (z-y)) z :=
        integral_integral_swap hprodI
      have hstart : (∫ z, (Iic x).indicator (smoothedSignedDensity k q) z) =
          ∫ z, ∫ y, (Iic x).indicator (fun z => k y * q (z-y)) z := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ≤ x <;> simp [hz, smoothedSignedDensity]
      rw [hstart, hswap]
      apply integral_congr_ae
      filter_upwards with y
      have hshift :
          (∫ z, (Iic x).indicator (fun z => k y * q (z-y)) z) =
          ∫ z, (Iic (x-y)).indicator (fun z => k y * q z) z := by
        have heq : (fun z => (Iic x).indicator (fun z => k y * q (z-y)) z) =
            (fun z => (Iic (x-y)).indicator (fun z => k y * q z) (z-y)) := by
          funext z
          by_cases hz : z ≤ x
          · simp [hz, sub_le_sub_right hz y]
          · simp [hz, show ¬ z-y ≤ x-y by linarith]
        rw [heq, integral_sub_right_eq_self]
      rw [hshift, integral_indicator measurableSet_Iic, integral_const_mul]
      rfl
    · intro t
      let ξ := -t / (2*Real.pi)
      have ht : -(2*Real.pi*ξ) = t := by dsimp [ξ]; field_simp
      have hc : (fun x => (smoothedSignedDensity k q x : ℂ)) =
          ((fun x => (k x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
            (fun x => (q x : ℂ))) := by
        funext x
        simp only [smoothedSignedDensity, convolution_def, ContinuousLinearMap.mul_apply']
        rw [← integral_complex_ofReal]
        congr 1
        funext y
        simp
      rw [← ht, charFunDensity_eq_fourier, hc]
      erw [Real.fourier_mul_convolution_eq (R := ℂ) hk.ofReal hq.ofReal]
      erw [← charFunDensity_eq_fourier, ← charFunDensity_eq_fourier]
      congr 1
      rw [charFun_apply_real, hwithC, charFunDensity]
      apply integral_congr_ae
      filter_upwards with y
      exact mul_comm _ _

  have finite_frequency_signed_smoothing
      (P : Measure ℝ) [IsProbabilityMeasure P] (k q : ℝ → ℝ)
      (hk : Integrable k) (hq : Integrable q) (hk0 : ∀ y, 0 ≤ k y)
      [IsProbabilityMeasure (smoothingLaw k)]
      (A : ℝ≥0) (hqA : ∀ x, |q x| ≤ A)
      (hG : LipschitzWith A (densityCDF q))
      (B h : ℝ) (hh : 0 ≤ h)
      (hcut : ∀ ξ : ℝ, B < |ξ| → charFun (smoothingLaw k) (-(2*Real.pi*ξ)) = 0)
      (hint : IntegrableOn (fun ξ : ℝ =>
        ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
          (Real.pi*|ξ|)) (Icc (-B) B))
      (htail : (smoothingLaw k).real {y : ℝ | h < |y|} < 1/2) :
      ∀ x : ℝ, |P.real (Iic x)-densityCDF q x| ≤
        ((∫ ξ in Icc (-B) B,
          ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
            (Real.pi*|ξ|)) + 2*(A:ℝ)*h) /
          (1-2*(smoothingLaw k).real {y : ℝ | h < |y|}) := by
    let ν := smoothingLaw k
    let Q := smoothedSignedDensity k q
    obtain ⟨hQint,hQcdf,hQcf⟩ := signed_convolution_bridge k q hk hq hk0
    have hwith (f : ℝ → ℝ) : (∫ y, f y ∂ν) = ∫ y, k y * f y := by
      rw [show ν = smoothingLaw k from rfl, smoothingLaw,
        integral_withDensity_eq_integral_toReal_smul₀
        hk.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
      simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul]
    have hQA (x : ℝ) : |Q x| ≤ A := by
      change |∫ y, k y*q (x-y)| ≤ A
      rw [← hwith]
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => q (x-y)) (C := (A:ℝ))
          (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hqA (x-y)))
    have hmod (a b : ℝ) (hab : a ≤ b) :
        (∫ y in Ioc a b, |Q y|) ≤ (A:ℝ)*(b-a) := by
      have hn := norm_setIntegral_le_of_norm_le_const
        (μ := (volume : Measure ℝ)) (s := Ioc a b) (f := fun y => |Q y|)
        (by simp [Real.volume_Ioc]) (fun y _ => by simpa using hQA y)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _),
        Real.volume_real_Ioc_of_le hab] using hn
    let f := fun ξ : ℝ =>
      ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ / (Real.pi*|ξ|)
    let D := ∫ ξ in Icc (-B) B, f ξ
    have hfind : Integrable ((Icc (-B) B).indicator f) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hint
    have hf0 (ξ : ℝ) : 0 ≤ f ξ := by dsimp [f]; positivity
    have hdifference (t : ℝ) : charFun (ν ∗ P) t - charFunDensity Q t =
        charFun ν t * (charFun P t-charFunDensity q t) := by
      rw [charFun_conv, hQcf]
      ring
    have hsmoothed (x : ℝ) : |(ν ∗ P).real (Iic x)-densityCDF Q x| ≤ D := by
      apply le_of_forall_pos_le_add
      intro ε hε
      let δ := ε/(2*(A:ℝ)+1)
      have hδ : 0 < δ := by dsimp [δ]; positivity
      let w := fun ξ : ℝ =>
        ‖charFun (ν ∗ P) (-(2*Real.pi*ξ))-charFunDensity Q (-(2*Real.pi*ξ))‖ *
          min (1/(Real.pi*|ξ|)) (1/(δ*Real.pi^2*ξ^2))
      have hw0 (ξ : ℝ) : 0 ≤ w ξ := by dsimp [w]; positivity
      have hwle (ξ : ℝ) : w ξ ≤ (Icc (-B) B).indicator f ξ := by
        by_cases hx : ξ ∈ Icc (-B) B
        · rw [indicator_of_mem hx]
          dsimp [w, f]
          rw [hdifference, norm_mul]
          calc
            _ ≤ (1 * ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖) *
                (1/(Real.pi*|ξ|)) := by
                  gcongr
                  · exact norm_charFun_le_one _
                  · exact min_le_left _ _
            _ = _ := by ring
        · have hξ : B < |ξ| := by
            by_contra hn
            have ha := abs_le.mp (le_of_not_gt hn)
            exact hx ha
          dsimp [w]
          rw [hdifference, hcut ξ hξ, zero_mul, norm_zero, zero_mul,
            indicator_of_notMem hx]
      have hwmeas : AEStronglyMeasurable w := by
        have hcq : Continuous fun ξ : ℝ => charFunDensity Q (-(2*Real.pi*ξ)) := by
          simp only [charFunDensity_eq_fourier]
          exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
            continuous_inner hQint.ofReal
        dsimp [w]
        exact (((measurable_charFun.comp (by fun_prop)).aestronglyMeasurable.sub
          hcq.aestronglyMeasurable).norm).mul ((by fun_prop : Measurable (fun ξ : ℝ => min (1/(Real.pi*|ξ|)) (1/(δ*Real.pi^2*ξ^2)))).aestronglyMeasurable)
      have hwint : Integrable w := hfind.mono' hwmeas
        (Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs,abs_of_nonneg (hw0 ξ)]; exact hwle ξ)
      have hwi : (∫ ξ, w ξ) ≤ D := by
        simpa only [D, integral_indicator measurableSet_Icc] using integral_mono hwint hfind hwle
      have hr := abs_measure_Iic_sub_densityCDF_le_charFun (P := ν ∗ P) hQint hδ hmod hwint x
      have hδε : 2*((A:ℝ)*δ) ≤ ε := by
        have heq : δ*(2*(A:ℝ)+1)=ε := by dsimp [δ]; field_simp
        nlinarith [hδ]
      exact hr.trans (by change (∫ ξ, w ξ)+2*((A:ℝ)*δ) ≤ D+ε; linarith)
    have hPcdf (x : ℝ) : (ν ∗ P).real (Iic x) = ∫ y, P.real (Iic (x-y)) ∂ν := by
      rw [← integral_indicator_one measurableSet_Iic]
      have hI : Integrable ((Iic x).indicator (1 : ℝ → ℝ)) (ν ∗ P) :=
        (integrable_const (1:ℝ)).indicator measurableSet_Iic
      rw [integral_conv hI]
      apply integral_congr_ae
      filter_upwards with y
      have heq : (fun z => (Iic x).indicator (1 : ℝ → ℝ) (y+z)) =
          (Iic (x-y)).indicator 1 := by
        funext z
        by_cases hz : z ≤ x-y
        · simp [hz, show y+z ≤ x by linarith]
        · simp [hz, show ¬ y+z ≤ x by linarith]
      rw [heq, integral_indicator_one measurableSet_Iic]
    have hGb (x : ℝ) : |densityCDF q x| ≤ ∫ y, |q y| := by
      exact (abs_integral_le_integral_abs).trans
        (setIntegral_le_integral hq.abs (Eventually.of_forall fun y => abs_nonneg _) )
    have hbounded : BddAbove (range fun x => |P.real (Iic x)-densityCDF q x|) := by
      refine ⟨1+∫ y,|q y|, ?_⟩
      rintro z ⟨x,rfl⟩
      exact (abs_sub _ _).trans (add_le_add
        (by simpa only [abs_of_nonneg (measureReal_nonneg)] using
          (measureReal_le_one (μ := P) (s := Iic x))) (hGb x))
    apply signed_smoothing_absorption (fun x => P.real (Iic x)) (densityCDF q) ν
      (fun _ _ hxy => measureReal_mono (Iic_subset_Iic.mpr hxy)) A hG hbounded h D hh htail
    intro x
    have hFi : Integrable (fun y => P.real (Iic (x-y))) ν := by
      simp_rw [← cdf_eq_real]
      apply Integrable.mono' (integrable_const 1)
        ((monotone_cdf (μ := P)).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      filter_upwards with y
      simpa only [Function.comp_def, Pi.sub_apply, id_eq, cdf_eq_real, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
        (measureReal_le_one (μ := P) (s := Iic (x-y)))
    have hGi : Integrable (fun y => densityCDF q (x-y)) ν := by
      apply Integrable.mono' (integrable_const (∫ y,|q y|))
        (hG.continuous.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      exact Eventually.of_forall fun y => by simpa only [Function.comp_def, Pi.sub_apply, id_eq, Real.norm_eq_abs] using hGb (x-y)
    rw [integral_sub hFi hGi, ← hPcdf, ← hQcdf]
    exact hsmoothed x

  have exists_uniform_finite_frequency_smoothing :
      ∃ H : ℝ, 0 < H ∧
        ∀ (P : Measure ℝ) [IsProbabilityMeasure P] (q : ℝ → ℝ),
        Integrable q → ∀ A : ℝ≥0, (∀ x, |q x| ≤ A) →
        LipschitzWith A (densityCDF q) →
        ∀ B : ℝ, 0 < B →
        IntegrableOn (fun ξ : ℝ =>
          ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
            (Real.pi*|ξ|)) (Icc (-B) B) →
        ∀ x : ℝ, |P.real (Iic x)-densityCDF q x| ≤
          2*(∫ ξ in Icc (-B) B,
            ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
              (Real.pi*|ξ|)) + 4*(A:ℝ)*H/B := by
    have hk0 (B : ℝ) (hB : 0 < B) (x : ℝ) : 0 ≤ fejerDensity B x := by
      dsimp [fejerDensity]; positivity
    have hkint (B : ℝ) (hB : 0 < B) : Integrable (fejerDensity B) := by
      have hi := (integrable_sin_div_sq.comp_mul_left' (mul_ne_zero Real.pi_ne_zero hB.ne')).const_mul B
      simpa only [fejerDensity, mul_assoc] using! hi
    have hkmass (B : ℝ) (hB : 0 < B) : (∫ x, fejerDensity B x) = 1 := by
      have heq : fejerDensity B = fejerKernel (2*Real.pi*B) := by
        funext x
        dsimp [fejerDensity, fejerKernel]
        congr 1
        · field_simp
        · congr 2 <;> ring
      rw [heq]
      exact integral_fejerKernel (by positivity)
    have hprob (B : ℝ) (hB : 0 < B) : IsProbabilityMeasure (smoothingLaw (fejerDensity B)) := by
      constructor
      rw [smoothingLaw, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (hkint B hB)
          (Eventually.of_forall (hk0 B hB)), hkmass B hB]
      simp
    have hreal (B : ℝ) (hB : 0 < B) (S : Set ℝ) (hS : MeasurableSet S) :
        (smoothingLaw (fejerDensity B)).real S = ∫ x in S, fejerDensity B x := by
      rw [← integral_indicator_one hS, smoothingLaw,
        integral_withDensity_eq_integral_toReal_smul₀
          (hkint B hB).aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
      simp only [ENNReal.toReal_ofReal (hk0 B hB _), smul_eq_mul]
      rw [← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ S <;> simp [hx]
    have hcut (B : ℝ) (hB : 0 < B) (ξ : ℝ) (hξ : B < |ξ|) :
        charFun (smoothingLaw (fejerDensity B)) (-(2*Real.pi*ξ)) = 0 := by
      have hcf : charFun (smoothingLaw (fejerDensity B)) (-(2*Real.pi*ξ)) =
          charFunDensity (fejerDensity B) (-(2*Real.pi*ξ)) := by
        rw [charFun_apply_real, smoothingLaw,
          integral_withDensity_eq_integral_toReal_smul₀
            (hkint B hB).aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp), charFunDensity]
        apply integral_congr_ae
        filter_upwards with y
        simp only [ENNReal.toReal_ofReal (hk0 B hB y), Complex.real_smul]
        exact mul_comm _ _
      rw [hcf, charFunDensity_eq_fourier]
      have heq : (fun x => (fejerDensity B x : ℂ)) = gTent B 0 := by
        funext x
        simp [fejerDensity, gTent, sqSincC]
      rw [heq, fourier_gTent hB 0 ξ]
      change (tent ((ξ-0)/B) : ℂ) = 0
      rw [sub_zero, tent_of_one_le_abs]
      · simp
      · rw [abs_div, abs_of_pos hB]
        exact (le_div_iff₀ hB).mpr (by linarith)
    have htailset (h : ℝ) : MeasurableSet {x : ℝ | h < |x|} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hempty : (⋂ h : ℝ, {x : ℝ | h < |x|}) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (lt_irrefl |x|) (mem_iInter.mp hx |x|)
    have htend : Tendsto (fun h : ℝ => ∫ x in {x : ℝ | h < |x|}, fejerDensity 1 x)
        atTop (𝓝 0) := by
      have ht := tendsto_setIntegral_of_antitone htailset
        (fun a b hab x hx => lt_of_le_of_lt hab hx) ⟨0,(hkint 1 (by norm_num)).integrableOn⟩
      simpa only [hempty, setIntegral_empty] using ht
    obtain ⟨H,hHpos,hHtail⟩ : ∃ H : ℝ, 0 < H ∧
        (∫ x in {x : ℝ | H < |x|}, fejerDensity 1 x) < 1/4 := by
      have hev := (tendsto_order.mp htend).2 (1/4) (by norm_num)
      obtain ⟨H,hH,hHv⟩ := ((eventually_gt_atTop 0).and hev).exists
      exact ⟨H,hH,hHv⟩
    refine ⟨H,hHpos,?_⟩
    intro P hP q hq A hqA hG B hB hint x
    haveI := hprob B hB
    have htail : (smoothingLaw (fejerDensity B)).real {y : ℝ | H/B < |y|} < 1/4 := by
      rw [hreal B hB _ (htailset _)]
      have heq : (fun y => ({y : ℝ | H/B < |y|}).indicator (fejerDensity B) y) =
          (fun y => B * ({y : ℝ | H < |y|}).indicator (fejerDensity 1) (B*y)) := by
        funext y
        have hiff : H/B < |y| ↔ H < |B*y| := by
          rw [div_lt_iff₀ hB, abs_mul, abs_of_pos hB, mul_comm]
        by_cases hy : H/B < |y|
        · have hy' : H < |B| * |y| := by simpa only [abs_mul] using hiff.mp hy
          simp [Set.indicator, hy, hy', fejerDensity]
        · have hy' : ¬ H < |B| * |y| := by simpa only [abs_mul] using (not_iff_not.mpr hiff).mp hy
          simp [Set.indicator, hy, hy']
      rw [← integral_indicator (htailset _), heq, integral_const_mul,
        Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hB), smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul, integral_indicator (htailset _)]
      exact hHtail
    have hm := finite_frequency_signed_smoothing P (fejerDensity B) q
      (hkint B hB) hq (hk0 B hB) A hqA hG B (H/B) (by positivity)
      (hcut B hB) hint (by linarith) x
    have hD : 0 ≤ ∫ ξ in Icc (-B) B,
        ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
          (Real.pi*|ξ|) := integral_nonneg (fun ξ => by positivity)
    have hden : 1/2 < 1-2*(smoothingLaw (fejerDensity B)).real {y : ℝ | H/B < |y|} := by
      linarith
    apply hm.trans
    apply (div_le_iff₀ (by linarith : 0 < 1-2*(smoothingLaw (fejerDensity B)).real {y : ℝ | H/B < |y|})).mpr
    have hnonneg : 0 ≤ 2*(∫ ξ in Icc (-B) B,
        ‖charFun P (-(2*Real.pi*ξ))-charFunDensity q (-(2*Real.pi*ξ))‖ /
          (Real.pi*|ξ|)) + 4*(A:ℝ)*H/B := by positivity
    have hh := mul_le_mul_of_nonneg_left hden.le hnonneg
    convert hh using 1 <;> ring

  exact exists_uniform_finite_frequency_smoothing

/-- Gaussian absorption bounds the growing low-frequency integral by an integrable polynomial envelope. -/
theorem low_frequency_integral_vanishes (p q a b δ : ℝ) (hp : 0≤p) (hq : 0≤q)
    (hV : 0<p*a^2+q*b^2) (hδ : 0≤δ) (ha : δ*|a|≤1) (hb : δ*|b|≤1)
    (habsorb : |p*a^3+q*b^3|/6*δ+(p*a^4+q*b^4)*δ^2 ≤ (p*a^2+q*b^2)/4) :
    Tendsto (fun w : ℝ => w * ∫ u in Icc 0 (δ*w),
      ‖charFun (centeredLaw (w^2) p q a b) (u/w)-
        (Real.exp (-(p*a^2+q*b^2)*u^2/2):ℂ)*
          (1+((p*a^3+q*b^3)*u^3/(6*w):ℝ)*Complex.I^3)‖/u)
      atTop (𝓝 0) := by
  have pair_charFun (p q : ℝ≥0) (a b t : ℝ) :
      charFun (pairLaw p q a b) t =
      Complex.exp ((p:ℂ)*(Complex.exp ((t*a:ℝ)*Complex.I)-1)+
        (q:ℂ)*(Complex.exp ((t*b:ℝ)*Complex.I)-1)) := by
    have hone (p : ℝ≥0) (u : ℝ) :
        (∫ n : ℕ, Complex.exp (((u*(n:ℝ):ℝ):ℂ)*Complex.I) ∂poissonMeasure p) =
          Complex.exp ((p:ℂ)*(Complex.exp ((u:ℂ)*Complex.I)-1)) := by
      have hh := charFun_map_cast_poissonMeasure p u
      rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)] at hh
      simpa only [Complex.ofReal_mul] using hh
    rw [pairLaw, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    have heq : (fun n : ℕ × ℕ => Complex.exp (((t*(a*(n.1:ℝ)+b*(n.2:ℝ)):ℝ):ℂ)*Complex.I)) =
        (fun n : ℕ × ℕ => Complex.exp ((((t*a)*(n.1:ℝ):ℝ):ℂ)*Complex.I)*
          Complex.exp ((((t*b)*(n.2:ℝ):ℝ):ℂ)*Complex.I)) := by
      funext n
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [← Complex.ofReal_mul]
    rw [heq, integral_prod_mul
      (fun n : ℕ => Complex.exp ((((t*a)*(n:ℝ):ℝ):ℂ)*Complex.I))
      (fun n : ℕ => Complex.exp ((((t*b)*(n:ℝ):ℝ):ℂ)*Complex.I)), hone, hone,
      ← Complex.exp_add]

  have centeredExponent_cubic_bound (lam p q a b t : ℝ)
      (hlam : 0≤lam) (hp : 0≤p) (hq : 0≤q) (ha : |t*a|≤1) (hb : |t*b|≤1) :
      ‖centeredExponent lam p q a b t + (lam*(p*a^2+q*b^2)*t^2/2:ℝ) -
          (lam*(p*a^3+q*b^3)*t^3/6:ℝ)*Complex.I^3‖ ≤
        lam*(p*a^4+q*b^4)*t^4 := by
    let R := fun z : ℂ => Complex.exp z-1-z-z^2/2-z^3/6
    have hscalar (u : ℝ) (hu : |u|≤1) : ‖R ((u:ℂ)*Complex.I)‖ ≤ u^4 := by
      have hnorm : ‖(u:ℂ)*Complex.I‖ = |u| := by simp
      have he := Complex.exp_bound (n:=4) (x:=(u:ℂ)*Complex.I) (by simpa only [hnorm] using hu) (by norm_num)
      have hsum : (∑ m ∈ Finset.range 4, ((u:ℂ)*Complex.I)^m/(m.factorial:ℂ)) =
          1+(u:ℂ)*Complex.I+((u:ℂ)*Complex.I)^2/2+((u:ℂ)*Complex.I)^3/6 := by
        norm_num [Finset.sum_range_succ]
      rw [hsum,hnorm] at he
      have heq : Complex.exp ((u:ℂ)*Complex.I) -
          (1+(u:ℂ)*Complex.I+((u:ℂ)*Complex.I)^2/2+((u:ℂ)*Complex.I)^3/6) =
          R ((u:ℂ)*Complex.I) := by dsimp [R]; ring
      rw [heq] at he
      norm_num at he
      have hu4 : |u|^4=u^4 := by rw [← abs_pow,abs_of_nonneg (by positivity)]
      rw [hu4] at he
      have hpos : 0 ≤ u^4 := by positivity
      nlinarith only [he,hpos]
    have h1 := hscalar (t*a) ha
    have h2 := hscalar (t*b) hb
    have heq : centeredExponent lam p q a b t + (lam*(p*a^2+q*b^2)*t^2/2:ℝ) -
          (lam*(p*a^3+q*b^3)*t^3/6:ℝ)*Complex.I^3 =
        (lam*p:ℝ)*R ((t*a:ℝ)*Complex.I)+(lam*q:ℝ)*R ((t*b:ℝ)*Complex.I) := by
      dsimp [centeredExponent,R]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [heq]
    calc
      _ ≤ ‖(lam*p:ℝ)*R ((t*a:ℝ)*Complex.I)‖+
          ‖(lam*q:ℝ)*R ((t*b:ℝ)*Complex.I)‖ := norm_add_le _ _
      _ = (lam*p)*‖R ((t*a:ℝ)*Complex.I)‖+(lam*q)*‖R ((t*b:ℝ)*Complex.I)‖ := by
        rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
          Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hlam hp),
          abs_of_nonneg (mul_nonneg hlam hq)]
      _ ≤ (lam*p)*(t*a)^4+(lam*q)*(t*b)^4 :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (mul_nonneg hlam hp))
          (mul_le_mul_of_nonneg_left h2 (mul_nonneg hlam hq))
      _ = lam*(p*a^4+q*b^4)*t^4 := by ring

  have centered_charFun (lam p q a b t : ℝ)
      (hlam : 0≤lam) (hp : 0≤p) (hq : 0≤q) :
      charFun (centeredLaw lam p q a b) t = Complex.exp (centeredExponent lam p q a b t) := by
    have hpmean := Real.coe_toNNReal (lam*p) (mul_nonneg hlam hp)
    have hqmean := Real.coe_toNNReal (lam*q) (mul_nonneg hlam hq)
    unfold centeredLaw
    simp only [sub_eq_add_neg]
    rw [charFun_map_add_const,pair_charFun,← Complex.exp_add]
    congr 1
    change (↑(↑(Real.toNNReal (lam*p)):ℝ):ℂ)*_+(↑(↑(Real.toNNReal (lam*q)):ℝ):ℂ)*_+_ = _
    rw [hpmean,hqmean]
    dsimp [centeredExponent]
    simp only [starRingEnd_apply,star_trivial]
    push_cast
    ring

  have local_characteristic_error (lam p q a b t : ℝ)
      (hlam : 0≤lam) (hp : 0≤p) (hq : 0≤q) (ha : |t*a|≤1) (hb : |t*b|≤1) :
      let Q := lam*(p*a^2+q*b^2)*t^2/2
      let R := lam*(p*a^4+q*b^4)*t^4
      let B := |lam*(p*a^3+q*b^3)*t^3/6|+R
      ‖charFun (centeredLaw lam p q a b) t -
        (Real.exp (-Q):ℂ) * (1+(lam*(p*a^3+q*b^3)*t^3/6:ℝ)*Complex.I^3)‖ ≤
        Real.exp (-Q+B)*(R+B^2) := by
    intro Q R B
    let K : ℂ := (lam*(p*a^3+q*b^3)*t^3/6:ℝ)*Complex.I^3
    let E := centeredExponent lam p q a b t
    let z := E+(Q:ℂ)
    have hrem : ‖z-K‖ ≤ R := centeredExponent_cubic_bound lam p q a b t hlam hp hq ha hb
    have hK : ‖K‖ = |lam*(p*a^3+q*b^3)*t^3/6| := by
      dsimp only [K]
      rw [norm_mul,norm_pow,Complex.norm_I,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs]
    have hB0 : 0 ≤ B := by dsimp [B,R]; positivity
    have hR0 : 0 ≤ R := by dsimp [R]; positivity
    have hz : ‖z‖ ≤ B := by
      calc
        ‖z‖ = ‖(z-K)+K‖ := by congr 1; ring
        _ ≤ ‖z-K‖+‖K‖ := norm_add_le _ _
        _ ≤ R+‖K‖ := add_le_add hrem le_rfl
        _ = B := by rw [hK]; dsimp [B]; ring
    have he := Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
    have heqsum : (∑ m ∈ Finset.range 2, z^m/(m.factorial:ℂ))=1+z := by
      norm_num [Finset.sum_range_succ]
    rw [heqsum] at he
    have hloc : ‖Complex.exp z-1-K‖ ≤ B^2*Real.exp B+R := by
      calc
        ‖Complex.exp z-1-K‖ = ‖(Complex.exp z-(1+z))+(z-K)‖ := by congr 1; ring
        _ ≤ ‖Complex.exp z-(1+z)‖+‖z-K‖ := norm_add_le _ _
        _ ≤ ‖z‖^2*Real.exp ‖z‖+R := add_le_add he hrem
        _ ≤ B^2*Real.exp B+R := by gcongr
    have hQnorm : ‖Complex.exp (-(Q:ℂ))‖ = Real.exp (-Q) := by rw [Complex.norm_exp]; simp
    have hsplit : Complex.exp E-Complex.exp (-(Q:ℂ))*(1+K) =
        Complex.exp (-(Q:ℂ))*(Complex.exp z-1-K) := by
      rw [mul_sub,mul_sub,← Complex.exp_add]
      have heq : -(Q:ℂ)+z=E := by dsimp [z]; ring
      rw [heq]
      ring
    rw [centered_charFun lam p q a b t hlam hp hq]
    change ‖Complex.exp E-(Real.exp (-Q):ℂ)*(1+K)‖ ≤ _
    rw [Complex.ofReal_exp,Complex.ofReal_neg,hsplit,norm_mul,hQnorm]
    calc
      _ ≤ Real.exp (-Q)*(B^2*Real.exp B+R) :=
        mul_le_mul_of_nonneg_left hloc (Real.exp_pos _).le
      _ ≤ Real.exp (-Q)*(B^2*Real.exp B+R*Real.exp B) := by
        gcongr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp hB0) hR0
      _ = (Real.exp (-Q)*Real.exp B)*(R+B^2) := by ring
      _ = Real.exp (-Q+B)*(R+B^2) := by rw [← Real.exp_add]

  have scaled_local_error (p q a b w u δ : ℝ) (hp : 0≤p) (hq : 0≤q)
      (hw : 1≤w) (hδ : 0≤δ) (ha : δ*|a|≤1) (hb : δ*|b|≤1)
      (habsorb : |p*a^3+q*b^3|/6*δ+(p*a^4+q*b^4)*δ^2 ≤ (p*a^2+q*b^2)/4)
      (hu : |u|≤δ*w) :
      ‖charFun (centeredLaw (w^2) p q a b) (u/w)-
        (Real.exp (-(p*a^2+q*b^2)*u^2/2):ℂ)*
          (1+((p*a^3+q*b^3)*u^3/(6*w):ℝ)*Complex.I^3)‖ ≤
      Real.exp (-(p*a^2+q*b^2)*u^2/4) *
        ((p*a^4+q*b^4)*u^4+2*(|p*a^3+q*b^3|/6*|u|^3)^2+
          2*((p*a^4+q*b^4)*u^4)^2)/w^2 := by
    have hwpos : 0<w := lt_of_lt_of_le zero_lt_one hw
    have hw0 := ne_of_gt hwpos
    let V := p*a^2+q*b^2
    let M := p*a^3+q*b^3
    let W := p*a^4+q*b^4
    let c := |M|/6
    let X := c*|u|^3
    let Y := W*u^4
    let B := X/w+Y/w^2
    have hW : 0≤W := by dsimp [W]; positivity
    have hc : 0≤c := by dsimp [c]; positivity
    have hX : 0≤X := by dsimp [X]; positivity
    have hY : 0≤Y := by dsimp [Y]; positivity
    have hB : 0≤B := by dsimp [B]; positivity
    have hratio : |u|/w≤δ := (div_le_iff₀ hwpos).mpr hu
    have hau : |u/w*a|≤1 := by
      rw [abs_mul,abs_div,abs_of_pos hwpos]
      exact (mul_le_mul_of_nonneg_right hratio (abs_nonneg a)).trans ha
    have hbu : |u/w*b|≤1 := by
      rw [abs_mul,abs_div,abs_of_pos hwpos]
      exact (mul_le_mul_of_nonneg_right hratio (abs_nonneg b)).trans hb
    have hl := local_characteristic_error (w^2) p q a b (u/w) (sq_nonneg _) hp hq hau hbu
    dsimp only at hl
    have hquad : w^2*V*(u/w)^2/2=V*u^2/2 := by field_simp <;> ring
    have hcubic : w^2*M*(u/w)^3/6=M*u^3/(6*w) := by field_simp <;> ring
    have hfourth : w^2*W*(u/w)^4=Y/w^2 := by dsimp [Y]; field_simp <;> ring
    have habs : |M*u^3/(6*w)|+Y/w^2=B := by
      rw [abs_div,abs_mul,abs_pow,abs_mul,abs_of_pos hwpos]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<6)]
      dsimp [B,X,c]
      ring
    change ‖_-(Real.exp (-(w^2*V*(u/w)^2/2)):ℂ)*(1+(w^2*M*(u/w)^3/6:ℝ)*Complex.I^3)‖ ≤
      Real.exp (-(w^2*V*(u/w)^2/2)+(|w^2*M*(u/w)^3/6|+w^2*W*(u/w)^4))*
        (w^2*W*(u/w)^4+(|w^2*M*(u/w)^3/6|+w^2*W*(u/w)^4)^2) at hl
    rw [hquad,hcubic,hfourth,habs] at hl
    have hbform : B=u^2*(c*(|u|/w)+W*(|u|/w)^2) := by
      have hcube : |u|^3=u^2*|u| := by rw [pow_succ,sq_abs]
      dsimp [B,X,Y]
      rw [hcube,div_pow,sq_abs]
      field_simp
      <;> ring
    have hbabsorb : B≤V*u^2/4 := by
      rw [hbform]
      have hm : c*(|u|/w)+W*(|u|/w)^2≤c*δ+W*δ^2 := by
        gcongr
      have hh := hm.trans habsorb
      have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg u)
      nlinarith only [hh']
    have hBw : B*w=X+Y/w := by dsimp [B]; field_simp <;> ring
    have hYw : Y/w≤Y := by
      apply (div_le_iff₀ hwpos).mpr
      nlinarith only [hY,hw]
    have hYw0 : 0≤Y/w := div_nonneg hY hwpos.le
    have hYw2 : (Y/w)^2≤Y^2 := sq_le_sq₀ hYw0 hY |>.mpr hYw
    have hb2 : (B*w)^2≤2*X^2+2*Y^2 := by
      rw [hBw]
      nlinarith only [sq_nonneg (X-Y/w),hYw2]
    have htotal : Y/w^2+B^2≤(Y+2*X^2+2*Y^2)/w^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hwpos)).mpr
      have heq : (Y/w^2+B^2)*w^2=Y+(B*w)^2 := by field_simp <;> ring
      rw [heq]
      linarith only [hb2]
    have hexp : Real.exp (-(V*u^2/2)+B) ≤ Real.exp (-V*u^2/4) := by
      apply Real.exp_le_exp.mpr
      linarith only [hbabsorb]
    have hfinal := hl.trans (mul_le_mul hexp htotal (by positivity) (Real.exp_pos _).le)
    simpa only [V,M,W,c,X,Y,neg_div,neg_mul,mul_div_assoc] using hfinal

  let V := p*a^2+q*b^2
  let W := p*a^4+q*b^4
  let c := |p*a^3+q*b^3|/6
  let P := fun u : ℝ => u^3*Real.exp (-(V/4)*u^2)*W+
    u^5*Real.exp (-(V/4)*u^2)*(2*c^2)+u^7*Real.exp (-(V/4)*u^2)*(2*W^2)
  let g := fun u : ℝ => ‖P u‖
  let f := fun w u : ℝ =>
    ‖charFun (centeredLaw (w^2) p q a b) (u/w)-
      (Real.exp (-V*u^2/2):ℂ)*(1+((p*a^3+q*b^3)*u^3/(6*w):ℝ)*Complex.I^3)‖/u
  have hW : 0≤W := by dsimp [W]; positivity
  have hVp : 0<V/4 := div_pos hV (by norm_num)
  have hpow (n : ℕ) : Integrable (fun u : ℝ => u^n*Real.exp (-(V/4)*u^2)) := by
    have hh := integrable_rpow_mul_exp_neg_mul_sq hVp (s:=(n:ℝ)) (by have hn := Nat.cast_nonneg (α:=ℝ) n; linarith only [hn])
    simpa only [Real.rpow_natCast] using hh
  have hg : Integrable g :=
    ((((hpow 3).mul_const W).add ((hpow 5).mul_const (2*c^2))).add
      ((hpow 7).mul_const (2*W^2))).norm
  have hg0 : ∀ u : ℝ, 0≤g u := fun u => norm_nonneg _
  have hgform (u : ℝ) (hu : 0≤u) :
      g u=Real.exp (-V*u^2/4)*(W*u^3+2*c^2*u^5+2*W^2*u^7) := by
    have hP : 0≤P u := by dsimp [P]; positivity
    rw [show g u=‖P u‖ from rfl, Real.norm_of_nonneg hP]
    dsimp [P]
    rw [show -(V/4)*u^2 = -V*u^2/4 by ring]
    ring
  have hpoint (w : ℝ) (hw : 1≤w) (u : ℝ) (hu : u ∈ Icc 0 (δ*w)) :
      0≤f w u ∧ f w u≤g u/w^2 := by
    refine ⟨div_nonneg (norm_nonneg _) hu.1,?_⟩
    by_cases hu0 : u=0
    · subst u
      dsimp [f]
      rw [div_zero]
      positivity
    have hup : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    have hwp : 0<w := lt_of_lt_of_le zero_lt_one hw
    have he := scaled_local_error p q a b w u δ hp hq hw hδ ha hb habsorb
      (by simpa only [abs_of_nonneg hu.1] using hu.2)
    have hh := div_le_div_of_nonneg_right he hup.le
    rw [abs_of_nonneg hu.1] at hh
    have halg :
        (Real.exp (-V*u^2/4)*(W*u^4+2*(c*u^3)^2+2*(W*u^4)^2)/w^2)/u = g u/w^2 := by
      rw [hgform u hu.1]
      field_simp
      <;> ring
    change f w u ≤ _ at hh
    exact hh.trans_eq halg
  have hmeas (w : ℝ) : AEStronglyMeasurable (f w) := by
    dsimp only [f]
    simp_rw [centered_charFun (w^2) p q a b _ (sq_nonneg _) hp hq]
    dsimp [centeredExponent]
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  have hbound (w : ℝ) (hw : 1≤w) :
      0≤(∫ u in Icc 0 (δ*w), f w u) ∧
      (∫ u in Icc 0 (δ*w), f w u) ≤ (∫ u, g u)/w^2 := by
    have hfi : IntegrableOn (f w) (Icc 0 (δ*w)) := by
      apply Integrable.mono' ((hg.div_const (w^2)).integrableOn) (hmeas w).restrict
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      rw [Real.norm_eq_abs,abs_of_nonneg (hpoint w hw u hu).1]
      exact (hpoint w hw u hu).2
    constructor
    · apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact (hpoint w hw u hu).1
    · calc
        _ ≤ ∫ u in Icc 0 (δ*w), g u/w^2 :=
          setIntegral_mono_on hfi (hg.div_const _).integrableOn measurableSet_Icc
            (fun u hu => (hpoint w hw u hu).2)
        _ ≤ ∫ u, g u/w^2 := setIntegral_le_integral (hg.div_const _)
          (Filter.Eventually.of_forall (fun u => div_nonneg (hg0 u) (sq_nonneg _)))
        _ = (∫ u, g u)/w^2 := integral_div (w^2) g
  have hlim : Tendsto (fun w : ℝ => w*((∫ u, g u)/w^2)) atTop (𝓝 0) := by
    have ht := tendsto_inv_atTop_zero.const_mul (∫ u, g u)
    convert ht using 1
    · funext w
      by_cases hw : w=0
      · simp [hw]
      · field_simp
    · simp
  apply squeeze_zero'
    (Filter.Eventually.mono (eventually_ge_atTop (1:ℝ)) (fun w hw =>
      mul_nonneg (le_trans zero_le_one hw) (hbound w hw).1))
    (Filter.Eventually.mono (eventually_ge_atTop (1:ℝ)) (fun w hw =>
      mul_le_mul_of_nonneg_left (hbound w hw).2 (le_trans zero_le_one hw))) hlim

end CompoundPoissonEdgeworth

end
