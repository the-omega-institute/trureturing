/- GID: D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform real-time Edgeworth, fixed-width local limits, and atom decay for irrational two-jump Poisson laws. -/

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

namespace CompoundPoissonEdgeworthProposal
open CompoundPoissonEdgeworth
open StatLean.HypothesisTesting hiding edgeworthCDF

def scaledError (p q a b w u : ℝ) : ℂ :=
  charFun (centeredLaw (w^2) p q a b) (u/w) -
    (Real.exp (-(p*a^2+q*b^2)*u^2/2):ℂ)*
      (1+((p*a^3+q*b^3)*u^3/(6*w):ℝ)*Complex.I^3)

def normalizedLaw (w p q a b : ℝ) : Measure ℝ :=
  (centeredLaw (w^2) p q a b).map (fun z => z/w)

def rateCountLaw (lam p q : ℝ) : Measure (ℕ × ℕ) :=
  (poissonMeasure (Real.toNNReal (lam*p))).prod (poissonMeasure (Real.toNNReal (lam*q)))

def rateScore (lam p q a b : ℝ) (n : ℕ × ℕ) : ℝ :=
  (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/Real.sqrt (lam*(p*a^2+q*b^2))

def rateCDF (lam p q a b x : ℝ) : ℝ :=
  (rateCountLaw lam p q).real {n | rateScore lam p q a b n≤x}

def rateEdgeworthCDF (lam p q a b x : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Iic x)+gaussianPDFReal 0 1 x*(p*a^3+q*b^3)*(1-x^2)/
    (6*Real.rpow (p*a^2+q*b^2) (3/2:ℝ)*Real.sqrt lam)

/-- For every fixed positive cutoff, the symmetric Fourier error is little-o of inverse square-root time. -/
theorem symmetric_cutoff_vanishes (p q a b C : ℝ) (hp : 0<p) (hq : 0<q)
    (hb0 : b ≠ 0) (hirr : Irrational (a/b)) (hC : 0<C) :
    Tendsto (fun w : ℝ => w * ∫ u in Icc (-C*w) (C*w),
      ‖scaledError p q a b w u‖/|u|) atTop (𝓝 0) := by
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

  have pair_charFun_norm (p q : ℝ≥0) (a b t : ℝ) :
      ‖charFun (pairLaw p q a b) t‖ = Real.exp (-damping p q a b t) := by
    rw [pair_charFun,Complex.norm_exp]
    congr 1
    simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.one_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]
    dsimp [damping]
    ring

  have damping_pos (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b ≠ 0) (hirr : Irrational (a/b)) {t : ℝ} (ht : t ≠ 0) :
      0 < damping p q a b t := by
    have h1 : 0 ≤ 1-Real.cos (t*a) := sub_nonneg.mpr (Real.cos_le_one _)
    have h2 : 0 ≤ 1-Real.cos (t*b) := sub_nonneg.mpr (Real.cos_le_one _)
    have hnonneg : 0 ≤ damping p q a b t := add_nonneg (mul_nonneg hp.le h1) (mul_nonneg hq.le h2)
    apply lt_of_le_of_ne hnonneg
    intro hz
    have hsum : p*(1-Real.cos (t*a))+q*(1-Real.cos (t*b))=0 := hz.symm
    have hc1 : Real.cos (t*a)=1 := by
      have h := (add_eq_zero_iff_of_nonneg (mul_nonneg hp.le h1) (mul_nonneg hq.le h2)).mp hsum
      have := (mul_eq_zero.mp h.1).resolve_left hp.ne'
      linarith only [this]
    have hc2 : Real.cos (t*b)=1 := by
      have h := (add_eq_zero_iff_of_nonneg (mul_nonneg hp.le h1) (mul_nonneg hq.le h2)).mp hsum
      have := (mul_eq_zero.mp h.2).resolve_left hq.ne'
      linarith only [this]
    obtain ⟨m,hm⟩ := (Real.cos_eq_one_iff _).mp hc1
    obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff _).mp hc2
    have hn0 : (n:ℝ) ≠ 0 := by
      intro h
      rw [h,zero_mul] at hn
      exact (mul_ne_zero ht hb) hn.symm
    apply hirr.ne_rational m n
    apply (div_eq_div_iff hb hn0).mpr
    have hpi : 2*Real.pi ≠ 0 := by positivity
    have hc : (t*a)*((n:ℝ)*(2*Real.pi)) = (t*b)*((m:ℝ)*(2*Real.pi)) := by rw [hm,hn]; ring
    have hh : t*(2*Real.pi)*(a*(n:ℝ)-b*(m:ℝ))=0 := by nlinarith only [hc]
    have := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero ht hpi)
    linarith only [this]

  have nonlattice_annulus_decay (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b ≠ 0) (hirr : Irrational (a/b)) (eta C : ℝ) (heta : 0<eta) :
      ∃ c : ℝ, 0<c ∧ ∀ lam : ℝ, 0≤lam → ∀ t : ℝ, eta≤|t| → |t|≤C →
        ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖ ≤
          Real.exp (-c*lam) := by
    let K := {t : ℝ | eta≤|t| ∧ |t|≤C}
    have hKclosed : IsClosed K :=
      (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed (by
      intro t ht
      exact abs_le.mp ht.2)
    have hc : Continuous (damping p q a b) := by unfold damping; fun_prop
    obtain ⟨c,hcpos,hclower⟩ := hK.exists_forall_le' hc.continuousOn (a:=0) (by
      intro t ht
      apply damping_pos p q a b hp hq hb hirr
      intro hz
      have := ht.1
      simp only [hz,abs_zero] at this
      linarith only [this,heta])
    refine ⟨c,hcpos,?_⟩
    intro lam hlam t hteta htC
    have hpmean : (Real.toNNReal (lam*p):ℝ)=lam*p := Real.coe_toNNReal _ (mul_nonneg hlam hp.le)
    have hqmean : (Real.toNNReal (lam*q):ℝ)=lam*q := Real.coe_toNNReal _ (mul_nonneg hlam hq.le)
    rw [pair_charFun_norm]
    have hdamp : damping (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b t =
        lam*damping p q a b t := by simp only [damping,hpmean,hqmean]; ring
    rw [hdamp]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (hclower t ⟨hteta,htC⟩) hlam
    linarith only [this]

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

  have annulus_integral_vanishes (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b ≠ 0) (hirr : Irrational (a/b)) (eta C : ℝ) (heta : 0<eta) :
      Tendsto (fun lam : ℝ => Real.sqrt lam *
        ∫ t in Icc eta C,
          ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖/t)
        atTop (𝓝 0) := by
    obtain ⟨c,hc,hdecay⟩ := nonlattice_annulus_decay p q a b hp hq hb hirr eta C heta
    let f := fun lam t =>
      ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖/t
    have hint (lam : ℝ) : IntegrableOn (f lam) (Icc eta C) := by
      have hcont : Continuous (fun t =>
          ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖) := by
        simp_rw [pair_charFun]
        fun_prop
      exact (hcont.continuousOn.div continuousOn_id
        (fun t ht => ne_of_gt (heta.trans_le ht.1))).integrableOn_compact isCompact_Icc
    have hnonneg (lam : ℝ) : 0 ≤ ∫ t in Icc eta C, f lam t := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact div_nonneg (norm_nonneg _) (heta.le.trans ht.1)
    have hupper (lam : ℝ) (hlam : 0≤lam) :
        (∫ t in Icc eta C, f lam t) ≤ volume.real (Icc eta C) * (Real.exp (-c*lam)/eta) := by
      have hh := setIntegral_mono_on (hint lam)
        (continuousOn_const.integrableOn_compact (μ:=volume) isCompact_Icc)
        measurableSet_Icc (fun t ht => show f lam t ≤ Real.exp (-c*lam)/eta from by
          have htpos := heta.trans_le ht.1
          have hbound := hdecay lam hlam t (by simpa only [abs_of_pos htpos] using ht.1) (by simpa only [abs_of_pos htpos] using ht.2)
          exact (div_le_div_of_nonneg_right hbound htpos.le).trans
            (div_le_div_of_nonneg_left (Real.exp_pos _).le heta ht.1))
      simpa only [setIntegral_const,smul_eq_mul] using hh
    have hexp : Tendsto (fun lam : ℝ => Real.sqrt lam*Real.exp (-c*lam)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2:ℝ) c hc
    have hlim : Tendsto (fun lam : ℝ => Real.sqrt lam *
        (volume.real (Icc eta C) * (Real.exp (-c*lam)/eta))) atTop (𝓝 0) := by
      convert hexp.const_mul (volume.real (Icc eta C)/eta) using 1
      · funext lam; ring
      · simp
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun lam => mul_nonneg (Real.sqrt_nonneg _) (hnonneg lam)))
      (Filter.Eventually.mono (eventually_ge_atTop (0:ℝ)) (fun lam hlam =>
        mul_le_mul_of_nonneg_left (hupper lam hlam) (Real.sqrt_nonneg _))) hlim

  have gaussian_correction_tail (V M δ C : ℝ) (hV : 0<V) (hδ : 0<δ) :
      Tendsto (fun w : ℝ => w * ∫ u in Icc (δ*w) (C*w),
        Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u) atTop (𝓝 0) := by
    let g := fun u : ℝ => ‖Real.exp (-V*u^2/2)*(1+|M| *u^3/6)‖
    let f := fun w u : ℝ => Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u
    have hg : Integrable g := by
      have h0 := integrable_exp_neg_mul_sq (show 0<V/2 by positivity)
      have h3 := integrable_rpow_mul_exp_neg_mul_sq (show 0<V/2 by positivity)
        (s:=((3:ℕ):ℝ)) (by norm_num)
      have hh := (h0.add (h3.mul_const (|M|/6))).norm
      convert hh using 1
      funext u
      simp only [Real.rpow_natCast, Pi.add_apply] at *
      dsimp only [g]
      congr 1
      ring_nf
    have hg0 (u : ℝ) : 0≤g u := norm_nonneg _
    have hpoint (w u : ℝ) (hw : 1≤w) (hu : δ*w≤u) :
        0≤w*f w u ∧ w*f w u≤g u/δ := by
      have hw0 : 0<w := lt_of_lt_of_le zero_lt_one hw
      have hu0 : 0<u := (mul_pos hδ hw0).trans_le hu
      have hgform : g u=Real.exp (-V*u^2/2)*(1+|M| *u^3/6) := by
        dsimp [g]
        rw [abs_of_nonneg (by positivity)]
      have hcoeff : |M| *u^3/(6*w)≤|M| *u^3/6 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      have hratio : w/u≤1/δ := (div_le_div_iff₀ hu0 hδ).mpr (by simpa [mul_comm] using hu)
      dsimp [f]
      constructor
      · positivity
      · rw [hgform]
        calc
          w*(Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u) =
            (w/u)*(Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))) := by ring
          _ ≤ (1/δ)*(Real.exp (-V*u^2/2)*(1+|M| *u^3/6)) :=
            mul_le_mul hratio (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
              (by positivity) (by positivity)
          _ = _ := by ring
    have hbound (w : ℝ) (hw : 1≤w) :
        0≤w*(∫ u in Icc (δ*w) (C*w), f w u) ∧
        w*(∫ u in Icc (δ*w) (C*w), f w u) ≤
          (∫ u in Ici (δ*w), g u)/δ := by
      have hmeas : AEStronglyMeasurable (fun u => w*f w u) := by
        dsimp [f]
        exact (by fun_prop : Measurable _).aestronglyMeasurable
      have hi : IntegrableOn (fun u => w*f w u) (Icc (δ*w) (C*w)) := by
        apply Integrable.mono' (hg.div_const δ).integrableOn hmeas.restrict
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        rw [Real.norm_of_nonneg (hpoint w u hw hu.1).1]
        exact (hpoint w u hw hu.1).2
      rw [← integral_const_mul]
      constructor
      · apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact (hpoint w u hw hu.1).1
      · calc
          _ ≤ ∫ u in Icc (δ*w) (C*w), g u/δ :=
            setIntegral_mono_on hi (hg.div_const δ).integrableOn measurableSet_Icc
              (fun u hu => (hpoint w u hw hu.1).2)
          _ ≤ ∫ u in Ici (δ*w), g u/δ :=
            setIntegral_mono_set (hg.div_const δ).integrableOn
              (Filter.Eventually.of_forall (fun u => div_nonneg (hg0 u) hδ.le))
              (Filter.Eventually.of_forall (fun u hu => hu.1))
          _ = _ := integral_div δ g
    have hlim : Tendsto (fun w : ℝ => (∫ u in Ici (δ*w), g u)/δ) atTop (𝓝 0) := by
      simpa using (tendsto_integral_Ici_zero (f:=g)
        (tendsto_id.const_mul_atTop hδ)).div_const δ
    apply squeeze_zero'
      ((eventually_ge_atTop (1:ℝ)).mono (fun w hw => (hbound w hw).1))
      ((eventually_ge_atTop (1:ℝ)).mono (fun w hw => (hbound w hw).2)) hlim

  have positive_cutoff_vanishes (p q a b δ C : ℝ) (hp : 0<p) (hq : 0<q)
      (hb0 : b ≠ 0) (hirr : Irrational (a/b)) (hV : 0<p*a^2+q*b^2)
      (hδ : 0<δ) (hδC : δ≤C) (ha : δ*|a|≤1) (hb : δ*|b|≤1)
      (habsorb : |p*a^3+q*b^3|/6*δ+(p*a^4+q*b^4)*δ^2 ≤ (p*a^2+q*b^2)/4) :
      Tendsto (fun w : ℝ => w * ∫ u in Icc 0 (C*w), ‖scaledError p q a b w u‖/u)
        atTop (𝓝 0) := by
    let V := p*a^2+q*b^2
    let M := p*a^3+q*b^3
    let f := fun w u => ‖scaledError p q a b w u‖/u
    let g := fun w u => ‖charFun (pairLaw (Real.toNNReal (w^2*p))
      (Real.toNNReal (w^2*q)) a b) (u/w)‖/u
    let k := fun w u => Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u
    have hfint (w l r : ℝ) (hl : 0≤l) : IntegrableOn (f w) (Icc l r) := by
      have hd : Differentiable ℝ (scaledError p q a b w) := by
        change Differentiable ℝ (fun u => scaledError p q a b w u)
        simp only [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp.le hq.le,
          centeredExponent]
        fun_prop
      have hz : scaledError p q a b w 0 = 0 := by
        simp [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp.le hq.le,
          centeredExponent]
      have hc : Continuous (dslope (scaledError p q a b w) 0) := by
        apply continuous_iff_continuousAt.mpr
        intro y
        by_cases hy : y=0
        · subst y; exact continuousAt_dslope_same.mpr (hd 0)
        · exact (continuousAt_dslope_of_ne hy).mpr hd.continuous.continuousAt
      apply hc.norm.integrableOn_Icc.congr
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0:ℝ)))] with u hu hu0
      have hun : u≠0 := by simpa using hu0
      rw [dslope_of_ne _ hun, slope_def_module, hz, sub_zero, sub_zero,
        norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (hl.trans hu.1)]
      dsimp [f]
      ring
    have hcenter (w t : ℝ) :
        ‖charFun (centeredLaw (w^2) p q a b) t‖ =
        ‖charFun (pairLaw (Real.toNNReal (w^2*p)) (Real.toNNReal (w^2*q)) a b) t‖ := by
      simp only [centeredLaw, sub_eq_add_neg]
      rw [charFun_map_add_const, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hpoint (w : ℝ) (hw : 1≤w) (u : ℝ) (hu : δ*w≤u) :
        f w u ≤ g w u+k w u := by
      have hw0 : 0<w := lt_of_lt_of_le zero_lt_one hw
      have hu0 : 0<u := (mul_pos hδ hw0).trans_le hu
      have hn : ‖(1:ℂ)+((M*u^3/(6*w):ℝ):ℂ)*Complex.I^3‖ ≤ 1+|M| *u^3/(6*w) := by
        calc
          _ ≤ ‖(1:ℂ)‖+‖((M*u^3/(6*w):ℝ):ℂ)*Complex.I^3‖ := norm_add_le _ _
          _ = _ := by simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_div, abs_mul, abs_of_pos hw0, abs_of_pos hu0]
      dsimp [f, scaledError, g, k]
      have hn2 := norm_sub_le (charFun (centeredLaw (w^2) p q a b) (u/w))
        ((Real.exp (-V*u^2/2):ℂ)*(1+((M*u^3/(6*w):ℝ):ℂ)*Complex.I^3))
      rw [hcenter, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] at hn2
      have hn3 := mul_le_mul_of_nonneg_left hn (Real.exp_pos (-V*u^2/2)).le
      apply (div_le_div_of_nonneg_right (hn2.trans (add_le_add le_rfl hn3)) hu0.le).trans_eq
      ring
    have hhigh (w : ℝ) (hw : 1≤w) :
        (∫ u in Icc (δ*w) (C*w), f w u) ≤
          (∫ t in Icc δ C, ‖charFun (pairLaw (Real.toNNReal (w^2*p))
            (Real.toNNReal (w^2*q)) a b) t‖/t) + ∫ u in Icc (δ*w) (C*w), k w u := by
      have hw0 : 0<w := lt_of_lt_of_le zero_lt_one hw
      have hgint : IntegrableOn (g w) (Icc (δ*w) (C*w)) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.div _ continuousOn_id (fun u hu => ne_of_gt ((mul_pos hδ hw0).trans_le hu.1))
        simp_rw [pair_charFun]
        fun_prop
      have hkint : IntegrableOn (k w) (Icc (δ*w) (C*w)) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.div _ continuousOn_id (fun u hu => ne_of_gt ((mul_pos hδ hw0).trans_le hu.1))
        fun_prop
      have hscale : (∫ u in Icc (δ*w) (C*w), g w u) =
          ∫ t in Icc δ C, ‖charFun (pairLaw (Real.toNNReal (w^2*p))
            (Real.toNNReal (w^2*q)) a b) t‖/t := by
        let j := fun t => ‖charFun (pairLaw (Real.toNNReal (w^2*p))
            (Real.toNNReal (w^2*q)) a b) t‖/t
        have heq : g w = fun u => w⁻¹ * j (u/w) := by
          funext u
          dsimp [g,j]
          field_simp
        rw [heq, integral_const_mul, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_right hδC hw0.le),
          intervalIntegral.integral_comp_div j hw0.ne']
        simp only [mul_div_cancel_right₀ _ hw0.ne', smul_eq_mul,
          ← mul_assoc, inv_mul_cancel₀ hw0.ne', one_mul]
        rw [intervalIntegral.integral_of_le hδC, ← integral_Icc_eq_integral_Ioc]
      calc
        _ ≤ ∫ u in Icc (δ*w) (C*w), (g w u+k w u) :=
          setIntegral_mono_on (hfint w _ _ (mul_nonneg hδ.le hw0.le)) (hgint.add hkint)
            measurableSet_Icc (fun u hu => hpoint w hw u hu.1)
        _ = _ := by rw [integral_add hgint hkint, hscale]
    have hsplit (w : ℝ) (hw : 1≤w) :
        (∫ u in Icc 0 (C*w), f w u) =
        (∫ u in Icc 0 (δ*w), f w u)+(∫ u in Icc (δ*w) (C*w), f w u) := by
      have hw0 : 0≤w := (zero_le_one.trans hw)
      have h0δ : 0≤δ*w := mul_nonneg hδ.le hw0
      have hδCw := mul_le_mul_of_nonneg_right hδC hw0
      have h0C : 0≤C*w := h0δ.trans hδCw
      simp_rw [integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le h0C, ← intervalIntegral.integral_of_le h0δ,
        ← intervalIntegral.integral_of_le hδCw,
        intervalIntegral.integral_add_adjacent_intervals
          ((intervalIntegrable_iff_integrableOn_Icc_of_le h0δ).mpr (hfint w _ _ le_rfl))
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hδCw).mpr (hfint w _ _ h0δ))]
    have hlow := low_frequency_integral_vanishes p q a b δ hp.le hq.le hV hδ.le ha hb habsorb
    have hraw := (annulus_integral_vanishes p q a b hp hq hb0 hirr δ C hδ).comp
      (tendsto_pow_atTop (by decide : (2:ℕ)≠0))
    have hraw' : Tendsto (fun w : ℝ => w * ∫ t in Icc δ C,
        ‖charFun (pairLaw (Real.toNNReal (w^2*p)) (Real.toNNReal (w^2*q)) a b) t‖/t)
        atTop (𝓝 0) := by
      apply hraw.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
      simp only [Function.comp_def, Real.sqrt_sq hw]
    have hgauss := gaussian_correction_tail V M δ C hV hδ
    have hlimit := hlow.add (hraw'.add hgauss)
    simp only [add_zero] at hlimit
    apply squeeze_zero' _ _ hlimit
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw
      apply mul_nonneg (zero_le_one.trans hw)
      exact setIntegral_nonneg measurableSet_Icc (fun u hu => div_nonneg (norm_nonneg _) hu.1)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw
      change w*(∫ u in Icc 0 (C*w), f w u) ≤ _
      rw [hsplit w hw]
      have hh := mul_le_mul_of_nonneg_left (hhigh w hw) (zero_le_one.trans hw)
      dsimp only [f, scaledError, k, V, M] at *
      linarith
  have scaledError_integrable (p q a b w l r : ℝ) (hp : 0≤p) (hq : 0≤q) :
      IntegrableOn (fun u => ‖scaledError p q a b w u‖/|u|) (Icc l r) := by
    have hd : Differentiable ℝ (scaledError p q a b w) := by
      change Differentiable ℝ (fun u => scaledError p q a b w u)
      simp only [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp hq,
        centeredExponent]
      fun_prop
    have hz : scaledError p q a b w 0 = 0 := by
      simp [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp hq,
        centeredExponent]
    have hc : Continuous (dslope (scaledError p q a b w) 0) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      by_cases hy : y=0
      · subst y; exact continuousAt_dslope_same.mpr (hd 0)
      · exact (continuousAt_dslope_of_ne hy).mpr hd.continuous.continuousAt
    apply hc.norm.integrableOn_Icc.congr
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0:ℝ)))] with u hu0
    have hun : u≠0 := by simpa using hu0
    rw [dslope_of_ne _ hun, slope_def_module, hz, sub_zero, sub_zero,
      norm_smul, norm_inv, Real.norm_eq_abs]
    ring
  have scaledError_neg_norm (p q a b w u : ℝ) :
      ‖scaledError p q a b w (-u)‖ = ‖scaledError p q a b w u‖ := by
    have heq : scaledError p q a b w (-u) =
        starRingEnd ℂ (scaledError p q a b w u) := by
      simp only [scaledError, neg_div, charFun_neg, map_sub, map_mul, map_add, map_one,
        map_pow, Complex.conj_ofReal, Complex.conj_I, neg_sq]
      push_cast
      ring
    rw [heq, Complex.norm_conj]

  let V := p*a^2+q*b^2
  let W := p*a^4+q*b^4
  let c := |p*a^3+q*b^3|/6
  have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg _))
    (mul_pos hq (sq_pos_of_ne_zero hb0))
  have hW : 0≤W := by dsimp [W]; positivity
  have hc : 0≤c := by dsimp [c]; positivity
  let δ := min 1 (min C (min (1/(|a|+1)) (min (1/(|b|+1)) (V/(4*(c+W+1))))))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := min_le_left _ _
  have hδC : δ≤C := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ≤1/(|a|+1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδb : δ≤1/(|b|+1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδV : δ≤V/(4*(c+W+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ha : δ*|a|≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < |a|+1)).mp hδa
    nlinarith
  have hb : δ*|b|≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < |b|+1)).mp hδb
    nlinarith
  have habsorb : c*δ+W*δ^2≤V/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*(c+W+1))).mp hδV
    have hs : δ^2≤δ := by nlinarith
    have hws := mul_le_mul_of_nonneg_left hs hW
    nlinarith
  have hpos := positive_cutoff_vanishes p q a b δ C hp hq hb0 hirr hV
    hδ hδC ha hb habsorb
  let f := fun w u => ‖scaledError p q a b w u‖/|u|
  have heven (w u : ℝ) : f w (-u)=f w u := by
    dsimp [f]
    rw [scaledError_neg_norm, abs_neg]
  have heq (w : ℝ) (hw : 0≤w) :
      (∫ u in Icc (-C*w) (C*w), f w u) =
        2*∫ u in Icc 0 (C*w), ‖scaledError p q a b w u‖/u := by
    have hB : 0≤C*w := mul_nonneg hC.le hw
    have hi1 := (intervalIntegrable_iff_integrableOn_Icc_of_le (neg_nonpos.mpr hB)).mpr
      (scaledError_integrable p q a b w (-(C*w)) 0 hp.le hq.le)
    have hi2 := (intervalIntegrable_iff_integrableOn_Icc_of_le hB).mpr
      (scaledError_integrable p q a b w 0 (C*w) hp.le hq.le)
    have hn : (∫ u in -(C*w)..0, f w u) = ∫ u in 0..C*w, f w u := by
      have hh := intervalIntegral.integral_comp_neg (f w) (a:=0) (b:=C*w)
      simp only [heven, neg_zero] at hh
      exact hh.symm
    have hmain : (∫ u in Icc (-C*w) (C*w), f w u) = 2*∫ u in Icc 0 (C*w), f w u := by
      rw [neg_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (neg_le_self hB),
        ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hn,
        intervalIntegral.integral_of_le hB, ← integral_Icc_eq_integral_Ioc]
      ring
    rw [hmain]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp [f]
    rw [abs_of_nonneg hu.1]
  have hlim := hpos.const_mul 2
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
  change 2*(w*∫ u in Icc 0 (C*w), ‖scaledError p q a b w u‖/u) =
    w*∫ u in Icc (-C*w) (C*w), f w u
  rw [heq w hw]
  ring

/-- Uniform first Edgeworth expansion, fixed-width Ioc local limit, and uniform atom decay at all sufficiently large real times. -/
theorem result (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
    (hb : b≠0) (hirr : Irrational (a/b)) :
    (∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
      Real.sqrt lam*|rateCDF lam p q a b x-rateEdgeworthCDF lam p q a b x| < ε) ∧
    (∀ h : ℝ, 0<h → ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ y : ℝ,
      |Real.sqrt lam*(rateCountLaw lam p q).real
        {n | y<a*(n.1:ℝ)+b*(n.2:ℝ) ∧ a*(n.1:ℝ)+b*(n.2:ℝ)≤y+h} -
        (h/Real.sqrt (p*a^2+q*b^2))*gaussianPDFReal 0 1
          ((y-lam*(p*a+q*b))/Real.sqrt (lam*(p*a^2+q*b^2)))|<ε) ∧
    (∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
      Real.sqrt lam*(rateCountLaw lam p q).real {n | rateScore lam p q a b n=x}<ε) := by
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

  have scaledError_integrable (p q a b w l r : ℝ) (hp : 0≤p) (hq : 0≤q) :
      IntegrableOn (fun u => ‖scaledError p q a b w u‖/|u|) (Icc l r) := by
    have hd : Differentiable ℝ (scaledError p q a b w) := by
      change Differentiable ℝ (fun u => scaledError p q a b w u)
      simp only [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp hq,
        centeredExponent]
      fun_prop
    have hz : scaledError p q a b w 0 = 0 := by
      simp [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp hq,
        centeredExponent]
    have hc : Continuous (dslope (scaledError p q a b w) 0) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      by_cases hy : y=0
      · subst y; exact continuousAt_dslope_same.mpr (hd 0)
      · exact (continuousAt_dslope_of_ne hy).mpr hd.continuous.continuousAt
    apply hc.norm.integrableOn_Icc.congr
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0:ℝ)))] with u hu0
    have hun : u≠0 := by simpa using hu0
    rw [dslope_of_ne _ hun, slope_def_module, hz, sub_zero, sub_zero,
      norm_smul, norm_inv, Real.norm_eq_abs]
    ring
  have scaledError_neg_norm (p q a b w u : ℝ) :
      ‖scaledError p q a b w (-u)‖ = ‖scaledError p q a b w u‖ := by
    have heq : scaledError p q a b w (-u) =
        starRingEnd ℂ (scaledError p q a b w u) := by
      simp only [scaledError, neg_div, charFun_neg, map_sub, map_mul, map_add, map_one,
        map_pow, Complex.conj_ofReal, Complex.conj_I, neg_sq]
      push_cast
      ring
    rw [heq, Complex.norm_conj]

  have normalized_uniform_edgeworth (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb0 : b≠0) (hirr : Irrational (a/b)) (hV : p*a^2+q*b^2=1) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        w*|(normalizedLaw w p q a b).real (Iic x)-
          StatLean.HypothesisTesting.edgeworthCDF ((p*a^3+q*b^3)/w) 1 x| < ε := by
    let M := p*a^3+q*b^3
    let P := fun w => normalizedLaw w p q a b
    let qD := fun w => StatLean.HypothesisTesting.edgeworthDensity (M/w) 1
    let f := fun w u => ‖scaledError p q a b w u‖/|u|
    let j := fun w ξ =>
      ‖charFun (P w) (-(2*Real.pi*ξ))-charFunDensity (qD w) (-(2*Real.pi*ξ))‖ /
        (Real.pi*|ξ|)
    have hprob (w : ℝ) : IsProbabilityMeasure (P w) := by
      haveI : IsProbabilityMeasure (pairLaw (Real.toNNReal (w^2*p))
          (Real.toNNReal (w^2*q)) a b) := by
        unfold pairLaw
        exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
      haveI : IsProbabilityMeasure (centeredLaw (w^2) p q a b) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    have hexpr (w u : ℝ) : charFun (P w) u-charFunDensity (qD w) u =
        scaledError p q a b w u := by
      have hfun : (fun z : ℝ => z/w) = (fun z => w⁻¹*z) := by funext z; ring
      dsimp only [P, normalizedLaw, qD]
      rw [hfun, charFun_map_mul_comp (by fun_prop),
        StatLean.HypothesisTesting.charFunDensity_edgeworthDensity]
      simp only [Nat.cast_one, Real.sqrt_one, inv_one, mul_one]
      dsimp [scaledError]
      rw [hV]
      have harg : w⁻¹*u=u/w := by ring
      rw [harg]
      simp only [Measure.map_id']
      congr 1
      rw [show -((u:ℂ)^2)/2 = ((-(u^2)/2:ℝ):ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
      rw [show Complex.I^3 = -Complex.I by norm_num [pow_succ]]
      dsimp [M]
      push_cast
      ring
    have hj (w ξ : ℝ) : j w ξ = 2*f w (2*Real.pi*ξ) := by
      dsimp [j]
      rw [hexpr, scaledError_neg_norm]
      dsimp [f]
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
      field_simp
    have hjint (w C : ℝ) (hw : 0≤w) (hC : 0<C) :
        IntegrableOn (j w) (Icc (-C*w) (C*w)) := by
      have hB : 0≤C*w := mul_nonneg hC.le hw
      have hπ : 0<2*Real.pi := by positivity
      have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le
        (mul_le_mul_of_nonneg_left (neg_le_self hB) hπ.le)).mpr
          (scaledError_integrable p q a b w ((2*Real.pi)*(-(C*w)))
            ((2*Real.pi)*(C*w)) hp.le hq.le)
      have hit := hi.comp_mul_left (c:=2*Real.pi)
      simp only [mul_div_cancel_left₀ _ hπ.ne'] at hit
      have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le (neg_le_self hB)).mp hit
      have heq : j w = fun ξ => 2*f w (2*Real.pi*ξ) := funext (hj w)
      rw [heq, neg_mul]
      exact hi'.const_mul 2
    have hintegral (w C : ℝ) (hw : 0≤w) (hC : 0<C) :
        (∫ ξ in Icc (-C*w) (C*w), j w ξ) =
          Real.pi⁻¹ * ∫ u in Icc (-(2*Real.pi*C)*w) ((2*Real.pi*C)*w), f w u := by
      have hB : 0≤C*w := mul_nonneg hC.le hw
      have hπ : 0<2*Real.pi := by positivity
      simp_rw [hj]
      rw [integral_const_mul, neg_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (neg_le_self hB),
        intervalIntegral.integral_comp_mul_left (f w) hπ.ne', smul_eq_mul,
        intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left (neg_le_self hB) hπ.le),
        ← integral_Icc_eq_integral_Ioc]
      have hleft : 2*Real.pi*-(C*w) = -(2*Real.pi*C)*w := by ring
      have hright : 2*Real.pi*(C*w) = (2*Real.pi*C)*w := by ring
      rw [hleft,hright]
      field_simp
    have hlimit (C : ℝ) (hC : 0<C) :
        Tendsto (fun w : ℝ => w*∫ ξ in Icc (-C*w) (C*w), j w ξ) atTop (𝓝 0) := by
      have hh := (symmetric_cutoff_vanishes p q a b (2*Real.pi*C)
        hp hq hb0 hirr (by positivity)).const_mul Real.pi⁻¹
      simp only [mul_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
      rw [hintegral w C hw hC]
      ring
    obtain ⟨H,hH,hSmooth⟩ := generic_finite_smoothing
    let A : ℝ≥0 := ⟨(Real.sqrt (2*Real.pi))⁻¹ * (1+66*|M|), by positivity⟩
    have hqA (w : ℝ) (hw : 1≤w) (x : ℝ) : |qD w x|≤A := by
      have hM : |M/w|≤|M| := by
        rw [abs_div, abs_of_nonneg (zero_le_one.trans hw)]
        exact div_le_self (abs_nonneg M) hw
      have hh := StatLean.HypothesisTesting.abs_edgeworthDensity_le (M/w) (n:=1) (by norm_num) x
      apply hh.trans
      change (Real.sqrt (2*Real.pi))⁻¹*(1+66*|M/w|) ≤
        (Real.sqrt (2*Real.pi))⁻¹*(1+66*|M|)
      gcongr
    have hqint (w : ℝ) : Integrable (qD w) :=
      StatLean.HypothesisTesting.integrable_edgeworthDensity (M/w) 1
    have hLip (w : ℝ) (hw : 1≤w) : LipschitzWith A (densityCDF (qD w)) := by
      have ho (x y : ℝ) (hxy : x≤y) :
          |densityCDF (qD w) y-densityCDF (qD w) x| ≤ (A:ℝ)*(y-x) := by
        have hs : densityCDF (qD w) y-densityCDF (qD w) x = ∫ t in Ioc x y, qD w t := by
          dsimp [densityCDF]
          rw [← Iic_union_Ioc_eq_Iic hxy,
            setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
              (hqint w).integrableOn (hqint w).integrableOn]
          ring
        rw [hs]
        have hh := norm_setIntegral_le_of_norm_le_const (μ:= (volume : Measure ℝ))
          (f:=qD w) (s:=Ioc x y) (by simp [Real.volume_Ioc])
          (fun t _ => by simpa only [Real.norm_eq_abs] using hqA w hw t)
        simpa only [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hxy] using hh
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, Real.dist_eq]
      rcases le_total x y with hxy | hyx
      · rw [abs_sub_comm (densityCDF (qD w) x), abs_of_nonpos (sub_nonpos.mpr hxy)]
        convert ho x y hxy using 1 <;> ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        exact ho y x hyx
    intro ε hε
    let C := 8*(A:ℝ)*H/ε+1
    have hC : 0<C := by dsimp [C]; positivity
    have hrem : 4*(A:ℝ)*H/C<ε/2 := by
      apply (div_lt_iff₀ hC).mpr
      have hCe : C*ε=8*(A:ℝ)*H+ε := by dsimp [C]; field_simp <;> ring
      nlinarith
    have he := (tendsto_order.mp (hlimit C hC)).2 (ε/4) (by positivity)
    filter_upwards [eventually_ge_atTop (1:ℝ), he] with w hw hew
    intro x
    have hw0 : 0<w := zero_lt_one.trans_le hw
    haveI := hprob w
    have hh := hSmooth (P w) (qD w) (hqint w) A (hqA w hw) (hLip w hw)
      (C*w) (by positivity) (by simpa only [neg_mul] using hjint w C hw0.le hC) x
    rw [StatLean.HypothesisTesting.densityCDF_edgeworthDensity] at hh
    have hm := mul_le_mul_of_nonneg_left hh hw0.le
    have heq : w*(2*(∫ ξ in Icc (-(C*w)) (C*w), j w ξ)+4*(A:ℝ)*H/(C*w)) =
        2*(w*∫ ξ in Icc (-C*w) (C*w), j w ξ)+4*(A:ℝ)*H/C := by
      rw [neg_mul]
      field_simp
      <;> ring
    change w*|(P w).real (Iic x)-StatLean.HypothesisTesting.edgeworthCDF (M/w) 1 x| < ε
    change w*|(P w).real (Iic x)-StatLean.HypothesisTesting.edgeworthCDF (M/w) 1 x| ≤
      w*(2*(∫ ξ in Icc (-(C*w)) (C*w), j w ξ)+4*(A:ℝ)*H/(C*w)) at hm
    rw [heq] at hm
    linarith

  have general_rate_uniform_edgeworth (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b≠0) (hirr : Irrational (a/b)) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
        Real.sqrt lam*|rateCDF lam p q a b x-rateEdgeworthCDF lam p q a b x| < ε := by
    let V := p*a^2+q*b^2
    let σ := Real.sqrt V
    have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg _))
      (mul_pos hq (sq_pos_of_ne_zero hb))
    have hσ : 0<σ := Real.sqrt_pos.mpr hV
    have hσ2 : σ^2=V := Real.sq_sqrt hV.le
    have hσ3 : σ^3=Real.rpow V (3/2:ℝ) := by
      dsimp [σ]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hV.le]
      norm_num
    have hbn : b/σ≠0 := div_ne_zero hb hσ.ne'
    have hirrn : Irrational ((a/σ)/(b/σ)) := by
      have heq : (a/σ)/(b/σ)=a/b := by field_simp
      rw [heq]
      exact hirr
    have hVn : p*(a/σ)^2+q*(b/σ)^2=1 := by
      field_simp
      nlinarith only [hσ2]
    have hMn : p*(a/σ)^3+q*(b/σ)^3=(p*a^3+q*b^3)/σ^3 := by ring
    have hmap (lam : ℝ) (hlam : 0≤lam) :
        normalizedLaw (Real.sqrt lam) p q (a/σ) (b/σ) =
          (rateCountLaw lam p q).map (rateScore lam p q a b) := by
      dsimp only [normalizedLaw, centeredLaw, pairLaw, rateCountLaw]
      rw [Real.sq_sqrt hlam, Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext n
      dsimp [Function.comp_def,rateScore]
      rw [Real.sqrt_mul hlam]
      change ((a/σ)*(n.1:ℝ)+(b/σ)*(n.2:ℝ)-lam*(p*(a/σ)+q*(b/σ)))/Real.sqrt lam =
        (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/(Real.sqrt lam*σ)
      ring
    have hcdf (lam : ℝ) (hlam : 0≤lam) (x : ℝ) :
        (normalizedLaw (Real.sqrt lam) p q (a/σ) (b/σ)).real (Iic x) =
          rateCDF lam p q a b x := by
      rw [hmap lam hlam]
      simp only [Measure.real, Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
        rateCDF]
      rfl
    have hcorr (lam x : ℝ) :
        StatLean.HypothesisTesting.edgeworthCDF
          ((p*(a/σ)^3+q*(b/σ)^3)/Real.sqrt lam) 1 x = rateEdgeworthCDF lam p q a b x := by
      rw [hMn,hσ3]
      simp only [StatLean.HypothesisTesting.edgeworthCDF,
        StatLean.HypothesisTesting.stdNormalCDF, StatLean.HypothesisTesting.normalCDF,
        StatLean.HypothesisTesting.stdNormalPDF_eq_gaussianPDFReal,
        Nat.cast_one, Real.sqrt_one, inv_one, mul_one]
      dsimp [rateEdgeworthCDF, V, Measure.real]
      ring
    intro ε hε
    have hh := Real.tendsto_sqrt_atTop.eventually
      (normalized_uniform_edgeworth p q (a/σ) (b/σ) hp hq hbn hirrn hVn ε hε)
    filter_upwards [eventually_ge_atTop (0:ℝ),hh] with lam hlam hh
    intro x
    simpa only [hcdf lam hlam x,hcorr lam x] using hh x

  have local_limit_of_edgeworth (F : ℝ → ℝ → ℝ) (κ : ℝ)
      (hF : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        w*|F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x|<ε)
      (d : ℝ) (hd : 0<d) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        |w*(F w (x+d/w)-F w x)-d*stdNormalPDF x|<ε := by
    let φ := stdNormalPDF
    let ψ := fun x : ℝ => φ x*(1-x^2)
    have hφzero : Tendsto φ (cocompact ℝ) (𝓝 0) := by
      have hh := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a:=1/2)
        (by norm_num) 0).div_const (Real.sqrt (2*Real.pi))
      convert hh using 1
      · funext x
        simp only [Real.rpow_zero,one_mul]
        dsimp [φ,stdNormalPDF]
        congr 2
        ring
      · simp
    have hφ2zero : Tendsto (fun x : ℝ => φ x*x^2) (cocompact ℝ) (𝓝 0) := by
      have hh := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a:=1/2)
        (by norm_num) 2).div_const (Real.sqrt (2*Real.pi))
      convert hh using 1
      · funext x
        rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
        dsimp [φ,stdNormalPDF]
        rw [show -(1/2:ℝ)*x^2 = -x^2/2 by ring]
        ring
      · simp
    have hψzero : Tendsto ψ (cocompact ℝ) (𝓝 0) := by
      convert hφzero.sub hφ2zero using 1
      · funext x; dsimp [ψ]; ring
      · simp
    have hφuc : UniformContinuous φ :=
      continuous_stdNormalPDF.uniformContinuous_of_tendsto_cocompact hφzero
    have hψcont : Continuous ψ :=
      continuous_stdNormalPDF.mul (continuous_const.sub (continuous_id.pow 2))
    have hψuc : UniformContinuous ψ := hψcont.uniformContinuous_of_tendsto_cocompact hψzero
    have hG (w x : ℝ) : StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x =
        stdNormalCDF x+κ/(6*w)*ψ x := by
      simp only [StatLean.HypothesisTesting.edgeworthCDF, Nat.cast_one,
        Real.sqrt_one, inv_one, mul_one]
      dsimp [ψ,φ]
      ring
    intro ε hε
    let η := ε/(8*(d+|κ|+1))
    have hη : 0<η := by dsimp [η]; positivity
    have hbudget : (2*d+|κ|)*η<ε/2 := by
      have heq : η*(8*(d+|κ|+1))=ε := by dsimp [η]; field_simp
      nlinarith [abs_nonneg κ]
    obtain ⟨δ₁,hδ₁,hφmod⟩ := Metric.uniformContinuous_iff.mp hφuc η hη
    obtain ⟨δ₂,hδ₂,hψmod⟩ := Metric.uniformContinuous_iff.mp hψuc η hη
    have hstep : Tendsto (fun w : ℝ => d/w) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul d
    have he1 := (tendsto_order.mp hstep).2 δ₁ hδ₁
    have he2 := (tendsto_order.mp hstep).2 δ₂ hδ₂
    filter_upwards [eventually_ge_atTop (1:ℝ),hF (ε/4) (by positivity),he1,he2]
      with w hw hFw hstep1 hstep2
    intro x
    have hw0 : 0<w := zero_lt_one.trans_le hw
    let y := x+d/w
    have hxy : x≤y := by
      have hh : 0≤d/w := by positivity
      dsimp [y]
      linarith
    have hydiff : y-x=d/w := by dsimp [y]; ring
    have hφint : IntegrableOn φ (Ioc x y) := integrable_stdNormalPDF.integrableOn
    have hcint : IntegrableOn (fun _ : ℝ => φ x) (Ioc x y) :=
      (continuousOn_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hPhiDiff : stdNormalCDF y-stdNormalCDF x=∫ t in Ioc x y, φ t := by
      simp only [stdNormalCDF_eq_setIntegral]
      rw [← Iic_union_Ioc_eq_Iic hxy,
        setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
          integrable_stdNormalPDF.integrableOn integrable_stdNormalPDF.integrableOn]
      ring
    have hdiff : (∫ t in Ioc x y, φ t-φ x) =
        stdNormalCDF y-stdNormalCDF x-(d/w)*φ x := by
      rw [integral_sub hφint hcint, ← hPhiDiff, setIntegral_const,
        Real.volume_real_Ioc_of_le hxy, smul_eq_mul,hydiff]
    have hbound : |∫ t in Ioc x y, φ t-φ x|≤η*(d/w) := by
      have hh := norm_setIntegral_le_of_norm_le_const (μ:=(volume:Measure ℝ))
        (s:=Ioc x y) (f:=fun t => φ t-φ x) (C:=η) (by simp [Real.volume_Ioc]) (by
          intro t ht
          have htx : dist t x<δ₁ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
            linarith [ht.2]
          simpa only [Real.dist_eq, Real.norm_eq_abs] using (hφmod htx).le)
      simpa only [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hxy,hydiff] using hh
    have hψbound : |ψ y-ψ x|<η := by
      apply hψmod
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy),hydiff]
      exact hstep2
    have heq : w*(F w y-F w x)-d*φ x =
        w*(F w y-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 y)-
        w*(F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x)+
        w*(∫ t in Ioc x y, φ t-φ x)+κ/6*(ψ y-ψ x) := by
      rw [hdiff,hG,hG]
      field_simp
      <;> ring
    rw [show x+d/w=y from rfl,heq]
    have h1 := hFw y
    have h2 := hFw x
    have h3 : w*|∫ t in Ioc x y, φ t-φ x|≤η*d := by
      have hh := mul_le_mul_of_nonneg_left hbound hw0.le
      calc
        _ ≤ w*(η*(d/w)) := hh
        _ = η*d := by field_simp <;> ring
    have h4 : |κ/6*(ψ y-ψ x)|≤|κ| *η := by
      rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6)]
      have hh := mul_le_mul_of_nonneg_left hψbound.le (abs_nonneg κ)
      have hn := mul_nonneg (abs_nonneg κ) (abs_nonneg (ψ y-ψ x))
      nlinarith
    calc
      _ ≤ |w*(F w y-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 y)|+
          |w*(F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x)|+
          |w*(∫ t in Ioc x y, φ t-φ x)|+|κ/6*(ψ y-ψ x)| := by
        exact (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ < ε := by
        simp only [abs_mul,abs_of_pos hw0] at h4 ⊢
        nlinarith [abs_nonneg κ]

  have general_rate_interval_local_limit (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b≠0) (hirr : Irrational (a/b)) (h : ℝ) (hh : 0<h) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ y : ℝ,
        |Real.sqrt lam*(rateCountLaw lam p q).real
          {n | y<a*(n.1:ℝ)+b*(n.2:ℝ) ∧ a*(n.1:ℝ)+b*(n.2:ℝ)≤y+h} -
          (h/Real.sqrt (p*a^2+q*b^2))*gaussianPDFReal 0 1
            ((y-lam*(p*a+q*b))/Real.sqrt (lam*(p*a^2+q*b^2)))|<ε := by
    let V := p*a^2+q*b^2
    let σ := Real.sqrt V
    let κ := (p*a^3+q*b^3)/Real.rpow V (3/2:ℝ)
    let F := fun w x => rateCDF (w^2) p q a b x
    have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg _))
      (mul_pos hq (sq_pos_of_ne_zero hb))
    have hσ : 0<σ := Real.sqrt_pos.mpr hV
    have hcorr (w x : ℝ) (hw : 0≤w) :
        rateEdgeworthCDF (w^2) p q a b x =
        StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x := by
      simp only [rateEdgeworthCDF, Real.sqrt_sq hw,
        StatLean.HypothesisTesting.edgeworthCDF,
        StatLean.HypothesisTesting.stdNormalCDF, StatLean.HypothesisTesting.normalCDF,
        StatLean.HypothesisTesting.stdNormalPDF_eq_gaussianPDFReal,
        Nat.cast_one,Real.sqrt_one,inv_one,mul_one]
      dsimp [κ,V,Measure.real]
      ring
    have hF : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        w*|F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x|<ε := by
      intro ε hε
      have he := (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).eventually
        (general_rate_uniform_edgeworth p q a b hp hq hb hirr ε hε)
      filter_upwards [eventually_ge_atTop (0:ℝ),he] with w hw he x
      simpa only [Real.sqrt_sq hw,hcorr w x hw] using he x
    intro ε hε
    have hi := Real.tendsto_sqrt_atTop.eventually
      (local_limit_of_edgeworth F κ hF (h/σ) (by positivity) ε hε)
    filter_upwards [eventually_ge_atTop (1:ℝ),hi] with lam hlam hi
    intro y
    have hlam0 : 0<lam := zero_lt_one.trans_le hlam
    have hw : 0<Real.sqrt lam := Real.sqrt_pos.mpr hlam0
    have hden : Real.sqrt (lam*V)=Real.sqrt lam*σ := Real.sqrt_mul hlam0.le V
    have hdenpos : 0<Real.sqrt (lam*V) := Real.sqrt_pos.mpr (mul_pos hlam0 hV)
    let x := (y-lam*(p*a+q*b))/Real.sqrt (lam*V)
    let z := x+(h/σ)/Real.sqrt lam
    have hxz : x≤z := by
      have hn : 0≤(h/σ)/Real.sqrt lam := by positivity
      dsimp [z]
      linarith
    let μ := (rateCountLaw lam p q).map (rateScore lam p q a b)
    haveI : IsProbabilityMeasure (rateCountLaw lam p q) := by dsimp [rateCountLaw]; infer_instance
    haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    have hCDF (t : ℝ) : μ.real (Iic t)=rateCDF lam p q a b t := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) measurableSet_Iic,rateCDF]
      rfl
    have hdiff : rateCDF lam p q a b z-rateCDF lam p q a b x=μ.real (Ioc x z) := by
      have heq : μ.real (Iic z)=μ.real (Iic x)+μ.real (Ioc x z) := by
        rw [← Iic_union_Ioc_eq_Iic hxz,
          measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
      rw [hCDF,hCDF] at heq
      linarith
    have hz : z=(y+h-lam*(p*a+q*b))/Real.sqrt (lam*V) := by
      dsimp [z,x]
      rw [hden]
      field_simp
      <;> ring
    have hinter : μ.real (Ioc x z)=(rateCountLaw lam p q).real
        {n | y<a*(n.1:ℝ)+b*(n.2:ℝ) ∧ a*(n.1:ℝ)+b*(n.2:ℝ)≤y+h} := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) measurableSet_Ioc]
      congr 2
      ext n
      change (x<rateScore lam p q a b n ∧ rateScore lam p q a b n≤z) ↔ _
      rw [hz]
      dsimp [x,rateScore]
      change ((y-lam*(p*a+q*b))/Real.sqrt (lam*V) <
        (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/Real.sqrt (lam*V) ∧
        (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/Real.sqrt (lam*V)≤
        (y+h-lam*(p*a+q*b))/Real.sqrt (lam*V)) ↔ _
      rw [div_lt_div_iff_of_pos_right hdenpos,div_le_div_iff_of_pos_right hdenpos]
      constructor <;> intro hn <;> constructor <;> linarith [hn.1,hn.2]
    have hhx := hi x
    dsimp only [F] at hhx
    rw [Real.sq_sqrt hlam0.le] at hhx
    change |Real.sqrt lam*(rateCDF lam p q a b z-rateCDF lam p q a b x)-
      (h/σ)*stdNormalPDF x|<ε at hhx
    rw [hdiff,hinter,stdNormalPDF_eq_gaussianPDFReal] at hhx
    exact hhx

  have atom_bound_of_continuous_comparison (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (G : ℝ → ℝ) (hG : Continuous G) (e : ℝ)
      (h : ∀ x : ℝ, |μ.real (Iic x)-G x|≤e) (x : ℝ) : μ.real {x}≤2*e := by
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hG.continuousAt (x:=x)) η hη
    let y := x-δ/2
    have hyx : y<x := by dsimp [y]; linarith
    have hdist : dist y x<δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hyx)]
      dsimp [y]
      linarith
    have hGy : |G y-G x|<η := by simpa only [Real.dist_eq] using hclose hdist
    have hsub : μ.real {x}≤μ.real (Ioc y x) := measureReal_mono (by
      intro z hz
      have hz' : z=x := by simpa using hz
      subst z
      exact ⟨hyx,le_rfl⟩)
    have hsplit : μ.real (Iic x)=μ.real (Iic y)+μ.real (Ioc y x) := by
      rw [← Iic_union_Ioc_eq_Iic hyx.le,
        measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
    have hx := (abs_le.mp (h x)).2
    have hy := (abs_le.mp (h y)).1
    have hGxy := (abs_lt.mp hGy).1
    linarith

  have general_rate_atom_vanishes (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b≠0) (hirr : Irrational (a/b)) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
        Real.sqrt lam*(rateCountLaw lam p q).real {n | rateScore lam p q a b n=x}<ε := by
    intro ε hε
    have hh := general_rate_uniform_edgeworth p q a b hp hq hb hirr (ε/4) (by positivity)
    filter_upwards [eventually_ge_atTop (1:ℝ),hh] with lam hlam hh
    intro x
    let μ := (rateCountLaw lam p q).map (rateScore lam p q a b)
    haveI : IsProbabilityMeasure (rateCountLaw lam p q) := by dsimp [rateCountLaw]; infer_instance
    haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    have hw : 0<Real.sqrt lam := Real.sqrt_pos.mpr (zero_lt_one.trans_le hlam)
    have hG : Continuous (rateEdgeworthCDF lam p q a b) := by
      have hc : Continuous (fun x : ℝ => (gaussianReal 0 1).real (Iic x)) := by
        have heq : (fun x : ℝ => (gaussianReal 0 1).real (Iic x)) =
            StatLean.HypothesisTesting.stdNormalCDF := rfl
        rw [heq]
        change Continuous (fun x => StatLean.HypothesisTesting.stdNormalCDF x)
        simp_rw [StatLean.HypothesisTesting.stdNormalCDF_eq_setIntegral]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hon : ContinuousOn (fun t : ℝ => ∫ u in Iic t, StatLean.HypothesisTesting.stdNormalPDF u) (Iic (x+1)) :=
          StatLean.HypothesisTesting.integrable_stdNormalPDF.integrableOn.continuousOn_Iic_primitive_Iic
        exact hon.continuousAt (Iic_mem_nhds (by linarith))
      have hpdf : Continuous (gaussianPDFReal 0 1) := by
        have ht := StatLean.HypothesisTesting.continuous_stdNormalPDF
        change Continuous (fun x => StatLean.HypothesisTesting.stdNormalPDF x) at ht
        simpa only [StatLean.HypothesisTesting.stdNormalPDF_eq_gaussianPDFReal] using ht
      change Continuous (fun x => rateEdgeworthCDF lam p q a b x)
      dsimp [rateEdgeworthCDF]
      fun_prop
    have hCDF (z : ℝ) : μ.real (Iic z)=rateCDF lam p q a b z := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) measurableSet_Iic,rateCDF]
      rfl
    have hbound := atom_bound_of_continuous_comparison μ (rateEdgeworthCDF lam p q a b) hG
      (ε/(4*Real.sqrt lam)) (by
        intro z
        rw [hCDF]
        have hh' := hh z
        rw [mul_comm] at hh'
        have hz := (lt_div_iff₀ hw).mpr hh'
        calc
          _ ≤ (ε/4)/Real.sqrt lam := hz.le
          _ = ε/(4*Real.sqrt lam) := by ring) x
    have hx : μ.real {x}=(rateCountLaw lam p q).real {n | rateScore lam p q a b n=x} := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
      rfl
    rw [hx] at hbound
    have hm := mul_le_mul_of_nonneg_left hbound hw.le
    have heq : Real.sqrt lam*(2*(ε/(4*Real.sqrt lam)))=ε/2 := by field_simp <;> norm_num
    rw [heq] at hm
    linarith

  exact ⟨general_rate_uniform_edgeworth p q a b hp hq hb hirr,
    fun h hh => general_rate_interval_local_limit p q a b hp hq hb hirr h hh,
    general_rate_atom_vanishes p q a b hp hq hb hirr⟩

end CompoundPoissonEdgeworthProposal
