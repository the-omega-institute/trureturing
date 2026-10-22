/-
Source-only continuation r4056, retaining the r4039 analytic bodies.
UNCOMPILED throughout; no native acceptance is claimed.
The sealed r4033 file is evidence, not an import: its false image split,
whole-line periodic carrier, and placeholder bridges are deliberately replaced.
Original definitions/owners and all signed modes are retained below.

The general weighted-lattice theorem consumed here was inspected in immutable
5860a2489d25479eed8a8fc3ee91719f543189ff, PeriodicEnergyTransport.lean.
Mathlib API inspection is at 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import D5.S3.Weil.ZetaCore.Defs
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaGamma.FormCore.LogGraph
import D5.S3.Weil.ZetaGamma.FormCore.Carleman
import D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound
import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation.BoundaryModeRates
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal Topology BigOperators

namespace D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

/-- Integrating conjugate-first polarization requires four L1 quadratic
integrands. This generic lemma records the required payments explicitly. -/
theorem weighted_linear_polarization {V X : Type*} [AddCommGroup V] [Module ℂ V]
    [MeasurableSpace X] (ν : Measure X) (μ : Measure ℝ)
    (A : ℝ → V →ₗ[ℂ] (X → ℂ)) (w : ℝ → ℝ) (f g : V)
    (hf : ∀ s, MemLp (A s f) 2 ν) (hg : ∀ s, MemLp (A s g) 2 ν)
    (h1 : Integrable (fun s => w s * ∫ x, Complex.normSq (A s (f+g) x) ∂ν) μ)
    (h2 : Integrable (fun s => w s * ∫ x, Complex.normSq (A s (f-g) x) ∂ν) μ)
    (h3 : Integrable (fun s => w s * ∫ x, Complex.normSq (A s (f+Complex.I • g) x) ∂ν) μ)
    (h4 : Integrable (fun s => w s * ∫ x, Complex.normSq (A s (f-Complex.I • g) x) ∂ν) μ) :
    Integrable (fun s => (w s : ℂ) * ∫ x, conj (A s f x)*A s g x ∂ν) μ ∧
    (∫ s, (w s : ℂ) * ∫ x, conj (A s f x)*A s g x ∂ν ∂μ) =
      qPol (∫ s, w s * ∫ x, Complex.normSq (A s (f+g) x) ∂ν ∂μ)
        (∫ s, w s * ∫ x, Complex.normSq (A s (f-g) x) ∂ν ∂μ)
        (∫ s, w s * ∫ x, Complex.normSq (A s (f+Complex.I • g) x) ∂ν ∂μ)
        (∫ s, w s * ∫ x, Complex.normSq (A s (f-Complex.I • g) x) ∂ν ∂μ) := by
  have hp (s : ℝ) :
      (w s : ℂ) * (∫ x, conj (A s f x)*A s g x ∂ν) =
        qPol (w s * ∫ x, Complex.normSq (A s (f+g) x) ∂ν)
          (w s * ∫ x, Complex.normSq (A s (f-g) x) ∂ν)
          (w s * ∫ x, Complex.normSq (A s (f+Complex.I • g) x) ∂ν)
          (w s * ∫ x, Complex.normSq (A s (f-Complex.I • g) x) ∂ν) := by
    rw [linear_integral_polarization (A s) f g (hf s) (hg s)]
    simp_rw [integral_complex_ofReal]
    unfold qPol
    push_cast
    ring
  have hcast (h : ℝ → ℝ) (hh : Integrable (fun s => w s * h s) μ) :
      Integrable (fun s => (w s : ℂ) * (h s : ℂ)) μ := by
    apply (Complex.ofRealCLM.integrable_comp hh).congr
    exact Eventually.of_forall fun s => Complex.ofReal_mul _ _
  have h1c := hcast (fun s => ∫ x, Complex.normSq (A s (f+g) x) ∂ν) h1
  have h2c := hcast (fun s => ∫ x, Complex.normSq (A s (f-g) x) ∂ν) h2
  have h3c := hcast (fun s => ∫ x, Complex.normSq (A s (f+Complex.I • g) x) ∂ν) h3
  have h4c := hcast (fun s => ∫ x, Complex.normSq (A s (f-Complex.I • g) x) ∂ν) h4
  have hi := ((h1c.sub h2c).sub ((h3c.sub h4c).const_mul Complex.I)).div_const 4
  refine ⟨hi.congr (Eventually.of_forall fun s => ?_), ?_⟩
  · simpa only [qPol,Pi.sub_apply] using (hp s).symm
  calc
    _ = ∫ s, qPol (w s * ∫ x, Complex.normSq (A s (f+g) x) ∂ν)
        (w s * ∫ x, Complex.normSq (A s (f-g) x) ∂ν)
        (w s * ∫ x, Complex.normSq (A s (f+Complex.I • g) x) ∂ν)
        (w s * ∫ x, Complex.normSq (A s (f-Complex.I • g) x) ∂ν) ∂μ :=
      integral_congr_ae (Eventually.of_forall hp)
    _ = _ := by
      rw [integral_qPol h1c h2c h3c h4c]

lemma continuous_weighted_moment_linear (L : ℝ) (w : ℝ → ℝ) (hw : Continuous w)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (a c : ℂ) :
    (∫ x in window L, (a*f x+c*g x)*(w x : ℂ)) =
      a*(∫ x in window L, f x*(w x : ℂ)) +
      c*(∫ x in window L, g x*(w x : ℂ)) := by
  have hfi : IntegrableOn (fun x => f x*(w x : ℂ)) (window L) :=
    (hf.mul (Complex.continuous_ofReal.comp hw)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgi : IntegrableOn (fun x => g x*(w x : ℂ)) (window L) :=
    (hg.mul (Complex.continuous_ofReal.comp hw)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simp_rw [add_mul,mul_assoc]
  rw [integral_add (hfi.const_mul a) (hgi.const_mul c),integral_const_mul,integral_const_mul]

lemma moment_polarization (L : ℝ) (w : ℝ → ℝ) (hw : Continuous w)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    qPol (Complex.normSq (∫ x in window L, (f x+g x)*(w x : ℂ)))
      (Complex.normSq (∫ x in window L, (f x-g x)*(w x : ℂ)))
      (Complex.normSq (∫ x in window L, (f x+Complex.I*g x)*(w x : ℂ)))
      (Complex.normSq (∫ x in window L, (f x-Complex.I*g x)*(w x : ℂ))) =
        conj (∫ x in window L, f x*(w x : ℂ)) * (∫ x in window L, g x*(w x : ℂ)) := by
  have h := continuous_weighted_moment_linear L w hw f g hf hg
  have h1 := h 1 1
  have h2 := h 1 (-1)
  have h3 := h 1 Complex.I
  have h4 := h 1 (-Complex.I)
  simp only [one_mul,neg_one_mul,neg_mul,← sub_eq_add_neg] at h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  exact (complex_polarization _ _).symm

/-- Literal one-rate MIXED equality, valid for arbitrary continuous complex
profiles, hence for every signed Fourier mode. No equality is assumed as a
premise: the four actual quadratic integrals above prove this by polarization. -/
theorem one_rate_mixed (L b : ℝ) [hL : Fact (0 < L)] (hb : 0 < b)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ s in Ioi 0, (Real.exp (-b*s) : ℂ) *
      ∫ x, conj (zeroExtension L (-L/2) f x-zeroExtension L (-L/2) f (x-s)) *
        (zeroExtension L (-L/2) g x-zeroExtension L (-L/2) g (x-s))) =
      (∫ s in Ioi 0, (Real.exp (-b*s) : ℂ) *
        ∫ x in window L, conj (f x-periodicExtension L (-L/2) f (x-s)) *
          (g x-periodicExtension L (-L/2) g (x-s))) +
      (2*Real.exp (-b*L)/(1-Real.exp (-b*L)) : ℝ) *
        (conj (coshMoment L b f)*coshMoment L b g -
          conj (sinhMoment L b f)*sinhMoment L b g) := by
  have hF := continuous_memLp_window L hf
  have hG := continuous_memLp_window L hg
  have h0 (u : ℝ → ℂ) (hu : Continuous u) :=
    (exp_energy_integrable L (-L/2) b hb u (continuous_memLp_window L hu)).1
  have hP (u : ℝ → ℂ) (hu : Continuous u) :=
    (exp_energy_integrable L (-L/2) b hb u (continuous_memLp_window L hu)).2
  have hfield0 (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure L (-L/2))) (s : ℝ) :
      MemLp (zeroGapMap L (-L/2) s u) 2 volume := by
    have hz := zero_extension_memLp L (-L/2) u hu
    exact hz.sub (hz.comp_measurePreserving (measurePreserving_sub_right volume s))
  have hfieldP (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure L (-L/2))) (s : ℝ) :
      MemLp (periodicGapMap L (-L/2) s u) 2 (windowMeasure L (-L/2)) :=
    hu.sub (periodic_shift_memLp L (-L/2) u hu s)
  have hfg : Continuous (f+g) := hf.add hg
  have hfm : Continuous (f-g) := hf.sub hg
  have hfi : Continuous (f+Complex.I • g) := hf.add (hg.const_smul Complex.I)
  have hfn : Continuous (f-Complex.I • g) := hf.sub (hg.const_smul Complex.I)
  have hz := (weighted_linear_polarization volume (volume.restrict (Ioi 0))
    (zeroGapMap L (-L/2)) (fun s => Real.exp (-b*s)) f g
    (hfield0 f hF) (hfield0 g hG) (h0 _ hfg) (h0 _ hfm) (h0 _ hfi) (h0 _ hfn)).2
  have hp := (weighted_linear_polarization (windowMeasure L (-L/2)) (volume.restrict (Ioi 0))
    (fun s => periodicGapMap L (-L/2) s) (fun s => Real.exp (-b*s)) f g
    (hfieldP f hF) (hfieldP g hG) (hP _ hfg) (hP _ hfm) (hP _ hfi) (hP _ hfn)).2
  have hQ1 := one_rate_quadratic L b hb (f+g) hfg
  have hQ2 := one_rate_quadratic L b hb (f-g) hfm
  have hQ3 := one_rate_quadratic L b hb (f+Complex.I • g) hfi
  have hQ4 := one_rate_quadratic L b hb (f-Complex.I • g) hfn
  have hC := moment_polarization L (fun x => Real.cosh (b*x)) (by fun_prop) f g hf hg
  have hS := moment_polarization L (fun x => Real.sinh (b*x)) (by fun_prop) f g hf hg
  have hwin : windowMeasure L (-L/2) = volume.restrict (window L) := by
    simp only [windowMeasure,window_eq]
  change (∫ s in Ioi 0, (Real.exp (-b*s) : ℂ) *
      ∫ x, conj (zeroGapMap L (-L/2) s f x)*zeroGapMap L (-L/2) s g x) = _
  rw [hz]
  have hpr :
      (∫ s in Ioi 0, (Real.exp (-b*s) : ℂ) *
        ∫ x in window L, conj (f x-periodicExtension L (-L/2) f (x-s)) *
          (g x-periodicExtension L (-L/2) g (x-s))) =
      qPol (∫ s in Ioi 0, Real.exp (-b*s)*periodicTranslationEnergy L (-L/2) (f+g) s)
        (∫ s in Ioi 0, Real.exp (-b*s)*periodicTranslationEnergy L (-L/2) (f-g) s)
        (∫ s in Ioi 0, Real.exp (-b*s)*periodicTranslationEnergy L (-L/2) (f+Complex.I • g) s)
        (∫ s in Ioi 0, Real.exp (-b*s)*periodicTranslationEnergy L (-L/2) (f-Complex.I • g) s) := by
    simpa only [periodicGapMap,LinearMap.coe_mk,AddHom.coe_mk,
      periodicTranslationEnergy,hwin] using hp
  rw [hpr]
  change qPol
    (∫ s in Ioi 0, Real.exp (-b*s)*zeroTranslationEnergy L (-L/2) (f+g) s)
    (∫ s in Ioi 0, Real.exp (-b*s)*zeroTranslationEnergy L (-L/2) (f-g) s)
    (∫ s in Ioi 0, Real.exp (-b*s)*zeroTranslationEnergy L (-L/2) (f+Complex.I • g) s)
    (∫ s in Ioi 0, Real.exp (-b*s)*zeroTranslationEnergy L (-L/2) (f-Complex.I • g) s) = _
  simp only [coshMoment,sinhMoment,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    at hQ1 hQ2 hQ3 hQ4 ⊢
  simp_rw [← Complex.ofReal_mul,integral_complex_ofReal]
  rw [hQ1,hQ2,hQ3,hQ4,← hC,← hS]
  unfold qPol
  push_cast
  ring

lemma lift_zeroMode (L : ℝ) [Fact (0 < L)] (n : ℤ) :
    AddCircle.liftIoc L (-L/2) (zeroMode L n) =
      AddCircle.liftIoc L (-L/2) (mode L n) := by
  funext c
  change zeroMode L n (AddCircle.equivIoc L (-L/2) c) =
    mode L n (AddCircle.equivIoc L (-L/2) c)
  have hx : (AddCircle.equivIoc L (-L/2) c : ℝ) ∈ window L := by
    rw [window_eq]
    exact (AddCircle.equivIoc L (-L/2) c).property
  exact Set.indicator_of_mem hx _

lemma periodicPair_eq_mode (L : ℝ) [Fact (0 < L)] (m n : ℤ) (s : ℝ) :
    periodicPair L m n s =
      ∫ x in window L, conj (mode L m x-periodicExtension L (-L/2) (mode L m) (x-s)) *
        (mode L n x-periodicExtension L (-L/2) (mode L n) (x-s)) := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hzero (k : ℤ) : zeroMode L k x = mode L k x := Set.indicator_of_mem hx _
  dsimp only
  rw [hzero m,hzero n]
  simp only [periodicExtension,lift_zeroMode]

/-- Consumer on the exact original all-signed mode definitions. -/
theorem rate_image_pairing (L b : ℝ) [Fact (0 < L)] (hb : 0 < b) (m n : ℤ) :
    (∫ s in Ioi 0, (Real.exp (-b*s) : ℂ)*displacementPair L m n s) =
      (∫ s in Ioi 0, (Real.exp (-b*s) : ℂ)*periodicPair L m n s) +
      (2*Real.exp (-b*L)/(1-Real.exp (-b*L)) : ℝ) *
        (conj (coshMoment L b (mode L m))*coshMoment L b (mode L n) -
          conj (sinhMoment L b (mode L m))*sinhMoment L b (mode L n)) := by
  have h := one_rate_mixed L b hb (mode L m) (mode L n)
    (mode_continuous L m) (mode_continuous L n)
  simpa only [displacementPair,zeroMode_eq,periodicPair_eq_mode] using h

/-- Fixed-index O(b^-2), with a concrete majorant, preserves u=0,v=0,u=-v,u=v. -/
lemma boundary_summand_bound (L b u v : ℝ) (hL : 0 < L) (hb : (1:ℝ)/2 ≤ b) :
    |(1-Real.exp (-b*L))*(b^2-u*v)/((b^2+u^2)*(b^2+v^2))| ≤
      (1+4*|u*v|)/b^2 := by
  have hb0 : 0 < b := by linarith
  have hb2 : (1:ℝ)/4 ≤ b^2 := by nlinarith
  have hden : 0 < (b^2+u^2)*(b^2+v^2) := by positivity
  have hdenb : b^2*b^2 ≤ (b^2+u^2)*(b^2+v^2) := by
    nlinarith [sq_nonneg u,sq_nonneg v,sq_nonneg (u*v),sq_nonneg b]
  have he : 0 ≤ 1-Real.exp (-b*L) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  have he1 : 1-Real.exp (-b*L) ≤ 1 := sub_le_self _ (Real.exp_pos _).le
  have hnum : |b^2-u*v| ≤ (1+4*|u*v|)*b^2 := by
    calc
      _ ≤ |b^2|+|u*v| := abs_sub _ _
      _ ≤ (1+4*|u*v|)*b^2 := by
        rw [abs_of_nonneg (sq_nonneg b)]
        nlinarith [abs_nonneg (u*v),mul_le_mul_of_nonneg_right hb2 (abs_nonneg (u*v))]
  rw [abs_div,abs_mul,abs_of_nonneg he,abs_of_pos hden]
  calc
    _ ≤ ((1+4*|u*v|)*b^2)/((b^2+u^2)*(b^2+v^2)) := by
      exact div_le_div_of_nonneg_right
        ((mul_le_of_le_one_left (abs_nonneg _) he1).trans hnum) hden.le
    _ ≤ ((1+4*|u*v|)*b^2)/(b^2*b^2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hdenb
    _ = _ := by field_simp [hb0.ne']

lemma inverse_rate_sq_summable : Summable (fun j : ℕ => (rate j ^ 2)⁻¹) := by
  have hs : Summable (fun j : ℕ => ((j:ℝ)^2)⁻¹) := by
    have h := Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<2)
    convert h using 1
    funext j
    rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.rpow_natCast]
  have hshift : Summable (fun j : ℕ => (((j:ℝ)+1)^2)⁻¹) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  apply (hshift.mul_left 4).of_nonneg_of_le
  · intro j; positivity
  · intro j
    have hrate : ((j:ℝ)+1)/2 ≤ rate j := by
      dsimp [rate]
      linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))]
    have hpos : 0 < rate j := rate_pos j
    have hj : 0 < (j:ℝ)+1 := by positivity
    calc
      (rate j^2)⁻¹ = 1/(rate j^2) := (one_div _).symm
      _ ≤ 4/((j:ℝ)+1)^2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hpos) (sq_pos_of_pos hj)).mpr
        nlinarith
      _ = 4*((((j:ℝ)+1)^2)⁻¹) := by rw [div_eq_mul_inv]

/-- The exact boundaryEntry series is absolutely convergent at every pair of
original signed indices, independently of any divided-difference branch. -/
theorem boundary_series_absolutely_summable (L : ℝ) (hL : 0 < L) (m n : ℤ) :
    Summable (fun j : ℕ =>
      |(1-Real.exp (-rate j*L))*(rate j^2-omega L m*omega L n)/
        ((rate j^2+omega L m^2)*(rate j^2+omega L n^2))|) := by
  apply (inverse_rate_sq_summable.mul_left (1+4*|omega L m*omega L n|)).of_nonneg_of_le
  · intro j; exact abs_nonneg _
  · intro j
    simpa only [div_eq_mul_inv] using
      boundary_summand_bound L (rate j) (omega L m) (omega L n) hL (rate_ge_half j)


/- r4056: substantive continuation starts here. -/

/-- The endpoint phase is real for EVERY signed index. -/
lemma mode_endpoint (L : ℝ) (hL : 0 < L) (n : ℤ) :
    Complex.exp (Complex.I * (omega L n : ℂ) * (L / 2 : ℝ)) =
      (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
  have ht : omega L n * (L / 2) = (n : ℝ) * Real.pi := by
    unfold omega
    field_simp [hL.ne']
    <;> ring
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, ht, Real.cos_int_mul_pi,
      Real.sin_int_mul_pi, mul_assoc, ← Complex.ofReal_zpow]

lemma mode_endpoint_neg (L : ℝ) (hL : 0 < L) (n : ℤ) :
    Complex.exp (Complex.I * (omega L n : ℂ) * (-L / 2 : ℝ)) =
      (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
  have ht : omega L n * (-L / 2) = -((n : ℝ) * Real.pi) := by
    unfold omega
    field_simp [hL.ne']
    <;> ring
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, ht, Real.cos_int_mul_pi,
      Real.sin_int_mul_pi, mul_assoc, ← Complex.ofReal_zpow]

lemma real_add_I_ne_zero (c u : ℝ) (hc : c ≠ 0) :
    (c : ℂ) + Complex.I * (u : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have : c = 0 := by simpa using hr
  exact hc this

lemma mode_exp_integrable (L c : ℝ) (n : ℤ) :
    IntegrableOn (fun x => mode L n x * (Real.exp (c*x) : ℂ)) (window L) := by
  exact ((mode_continuous L n).mul (by fun_prop)).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

/-- A genuine exponential antiderivative on the literal Ioc carrier. -/
lemma mode_exp_integral (L c : ℝ) (hL : 0 < L) (hc : c ≠ 0) (n : ℤ) :
    (∫ x in window L, mode L n x * (Real.exp (c*x) : ℂ)) =
      (2 * (((-1 : ℝ)^n : ℝ) : ℂ) * (Real.sinh (c*L/2) : ℂ)) /
        ((Real.sqrt L : ℂ) * ((c : ℂ) + Complex.I * (omega L n : ℂ))) := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hz := real_add_I_ne_zero c (omega L n) hc
  have hfun (x : ℝ) : mode L n x * (Real.exp (c*x) : ℂ) =
      (Real.sqrt L : ℂ)⁻¹ *
        Complex.exp (((c : ℂ) + Complex.I * (omega L n : ℂ)) * (x : ℂ)) := by
    unfold mode
    rw [Complex.ofReal_exp]
    calc
      _ = (Real.sqrt L : ℂ)⁻¹ *
          (Complex.exp (Complex.I*(omega L n:ℂ)*(x:ℂ)) *
            Complex.exp ((c*x:ℝ):ℂ)) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring
  simp_rw [hfun]
  rw [integral_const_mul, window,
    ← intervalIntegral.integral_of_le (by linarith : -L/2 ≤ L/2),
    _root_.integral_exp_mul_complex hz]
  have hp : Complex.exp
      (((c : ℂ) + Complex.I * (omega L n : ℂ)) * (L/2 : ℝ)) =
      (Real.exp (c*L/2) : ℂ) * (((-1 : ℝ)^n : ℝ) : ℂ) := by
    have he : (((c : ℂ)+Complex.I*(omega L n:ℂ))*(L/2:ℝ)) =
        ((c*L/2:ℝ):ℂ)+Complex.I*(omega L n:ℂ)*(L/2:ℝ) := by
      push_cast
      ring
    rw [he, Complex.exp_add, mode_endpoint L hL n, ← Complex.ofReal_exp]
  have hm : Complex.exp
      (((c : ℂ) + Complex.I * (omega L n : ℂ)) * (-L/2 : ℝ)) =
      (Real.exp (-(c*L/2)) : ℂ) * (((-1 : ℝ)^n : ℝ) : ℂ) := by
    have he : (((c : ℂ)+Complex.I*(omega L n:ℂ))*(-L/2:ℝ)) =
        ((-(c*L/2):ℝ):ℂ)+Complex.I*(omega L n:ℂ)*(-L/2:ℝ) := by
      push_cast
      ring
    rw [he, Complex.exp_add, mode_endpoint_neg L hL n, ← Complex.ofReal_exp]
  rw [hp, hm, Real.sinh_eq]
  push_cast
  field_simp [hs, hz]
  <;> ring

/-- Signed cosh moment, without a zero/opposite-mode exclusion. -/
theorem coshMoment_mode (L b : ℝ) (hL : 0 < L) (hb : 0 < b) (n : ℤ) :
    coshMoment L b (mode L n) =
      ((2 * (-1 : ℝ)^n * b * Real.sinh (b*L/2) /
        (Real.sqrt L * (b^2 + omega L n^2)) : ℝ) : ℂ) := by
  have hp := mode_exp_integral L b hL hb.ne' n
  have hm := mode_exp_integral L (-b) hL (neg_ne_zero.mpr hb.ne') n
  have hsplit : coshMoment L b (mode L n) =
      ((∫ x in window L, mode L n x * (Real.exp (b*x) : ℂ)) +
        (∫ x in window L, mode L n x * (Real.exp (-b*x) : ℂ))) / 2 := by
    unfold coshMoment
    rw [← integral_add (mode_exp_integrable L b n) (mode_exp_integrable L (-b) n),
      ← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; rw [Real.cosh_eq]; push_cast; ring
  rw [hsplit, hp, hm]
  have hs := (Real.sqrt_pos.mpr hL).ne'
  have hd : b^2 + omega L n^2 ≠ 0 := ne_of_gt (by positivity)
  have hz := real_add_I_ne_zero b (omega L n) hb.ne'
  have hz' := real_add_I_ne_zero (-b) (omega L n) (neg_ne_zero.mpr hb.ne')
  simp only [neg_mul, neg_div, Real.sinh_neg, Complex.ofReal_neg]
  push_cast
  have hdc : (b:ℂ)^2 + (omega L n:ℂ)^2 ≠ 0 := by exact_mod_cast hd
  have hzc : -(b:ℂ) + Complex.I * (omega L n:ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg] using hz'
  field_simp [Complex.ofReal_ne_zero.mpr hs, hdc, hz, hzc]
  <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The minus-i sign comes from the DIFFERENCE of the two exponential integrals. -/
theorem sinhMoment_mode (L b : ℝ) (hL : 0 < L) (hb : 0 < b) (n : ℤ) :
    sinhMoment L b (mode L n) =
      -Complex.I * ((2 * (-1 : ℝ)^n * omega L n * Real.sinh (b*L/2) /
        (Real.sqrt L * (b^2 + omega L n^2)) : ℝ) : ℂ) := by
  have hp := mode_exp_integral L b hL hb.ne' n
  have hm := mode_exp_integral L (-b) hL (neg_ne_zero.mpr hb.ne') n
  have hsplit : sinhMoment L b (mode L n) =
      ((∫ x in window L, mode L n x * (Real.exp (b*x) : ℂ)) -
        (∫ x in window L, mode L n x * (Real.exp (-b*x) : ℂ))) / 2 := by
    unfold sinhMoment
    rw [← integral_sub (mode_exp_integrable L b n) (mode_exp_integrable L (-b) n),
      ← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; rw [Real.sinh_eq]; push_cast; ring
  rw [hsplit, hp, hm]
  have hs := (Real.sqrt_pos.mpr hL).ne'
  have hd : b^2 + omega L n^2 ≠ 0 := ne_of_gt (by positivity)
  have hz := real_add_I_ne_zero b (omega L n) hb.ne'
  have hz' := real_add_I_ne_zero (-b) (omega L n) (neg_ne_zero.mpr hb.ne')
  simp only [neg_mul, neg_div, Real.sinh_neg, Complex.ofReal_neg]
  push_cast
  have hdc : (b:ℂ)^2 + (omega L n:ℂ)^2 ≠ 0 := by exact_mod_cast hd
  have hzc : -(b:ℂ) + Complex.I * (omega L n:ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg] using hz'
  field_simp [Complex.ofReal_ne_zero.mpr hs, hdc, hz, hzc]
  <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma hyperbolic_rate_factor (L b : ℝ) (hL : 0 < L) (hb : 0 < b) :
    8 * Real.exp (-b*L) * Real.sinh (b*L/2)^2 /
      (1-Real.exp (-b*L)) = 2*(1-Real.exp (-b*L)) := by
  have hr : 1-Real.exp (-b*L) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith)))
  have he : Real.exp (-b*L) = (Real.exp (b*L/2) * Real.exp (b*L/2))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1 <;> ring
  apply (div_eq_iff hr).mpr
  rw [Real.sinh_eq, he, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  <;> ring

/-- Explicit boundary algebra consumes BOTH signed moments of the actual modes. -/
theorem mode_image_form (L b : ℝ) (hL : 0 < L) (hb : 0 < b) (m n : ℤ) :
    (2*Real.exp (-b*L)/(1-Real.exp (-b*L)) : ℝ) *
      (conj (coshMoment L b (mode L m))*coshMoment L b (mode L n) -
        conj (sinhMoment L b (mode L m))*sinhMoment L b (mode L n)) =
      (((2/L)*(-1 : ℝ)^(m+n) *
        ((1-Real.exp (-b*L))*(b^2-omega L m*omega L n) /
          ((b^2+omega L m^2)*(b^2+omega L n^2))) : ℝ) : ℂ) := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hd₁ : b^2+omega L m^2 ≠ 0 := ne_of_gt (by positivity)
  have hd₂ : b^2+omega L n^2 ≠ 0 := ne_of_gt (by positivity)
  have hr : 1-Real.exp (-b*L) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith)))
  have hcore :
      conj (coshMoment L b (mode L m))*coshMoment L b (mode L n) -
        conj (sinhMoment L b (mode L m))*sinhMoment L b (mode L n) =
      ((4*(-1 : ℝ)^(m+n)*Real.sinh (b*L/2)^2*(b^2-omega L m*omega L n) /
        ((Real.sqrt L)^2*(b^2+omega L m^2)*(b^2+omega L n^2)) : ℝ) : ℂ) := by
    rw [coshMoment_mode L b hL hb m, coshMoment_mode L b hL hb n,
      sinhMoment_mode L b hL hb m, sinhMoment_mode L b hL hb n]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    push_cast
    field_simp [hs, Complex.ofReal_ne_zero.mpr hd₁, Complex.ofReal_ne_zero.mpr hd₂]
    <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [hcore, Real.sq_sqrt hL.le, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  calc
    _ = (8*Real.exp (-b*L)*Real.sinh (b*L/2)^2/(1-Real.exp (-b*L))) *
        ((-1 : ℝ)^(m+n)*(b^2-omega L m*omega L n) /
          (L*(b^2+omega L m^2)*(b^2+omega L n^2))) := by
      field_simp [hL.ne', hd₁, hd₂, hr]
      <;> ring
    _ = _ := by
      rw [hyperbolic_rate_factor L b hL hb]
      field_simp [hL.ne', hd₁, hd₂]
      <;> ring

/-- Actual Ioc orthogonality via the original AddCircle coefficient integral.
The factor 1/L is precisely the square of the normalization 1/sqrt L. -/
theorem mode_inner (L : ℝ) [hL : Fact (0 < L)] (m n : ℤ) :
    (∫ x in window L, conj (mode L m x)*mode L n x) =
      if m=n then (1 : ℂ) else 0 := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL.out).ne'
  have hs2 : (Real.sqrt L : ℂ)^2 = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt hL.out.le
  have hp (x : ℝ) : conj (mode L m x)*mode L n x =
      (1/L : ℝ) * (_root_.fourier (-m) (x : AddCircle L) *
        _root_.fourier n (x : AddCircle L)) := by
    rw [mode_fourier, mode_fourier, _root_.fourier_neg]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp [hs, hL.out.ne']
    <;> simp only [hs2] <;> ring
  simp_rw [hp]
  rw [integral_const_mul]
  have hc := _root_.fourierCoeff_eq_intervalIntegral
    (_root_.fourier n : AddCircle L → ℂ) m (-L/2)
  rw [show -L/2+L=L/2 by ring,
    intervalIntegral.integral_of_le (by linarith [hL.out] : -L/2 ≤ L/2)] at hc
  change _ = (1/L : ℝ) • ∫ x in window L,
    _root_.fourier (-m) (x : AddCircle L) • _root_.fourier n (x : AddCircle L) at hc
  simp only [smul_eq_mul,Complex.real_smul] at hc
  rw [← hc]
  simp only [_root_.fourierCoeff_fourier, Pi.single_apply]

lemma periodicExtension_mode (L : ℝ) [Fact (0 < L)] (n : ℤ) (x : ℝ) :
    periodicExtension L (-L/2) (mode L n) x = mode L n x := by
  unfold periodicExtension
  rw [lift_mode, mode_fourier]

lemma mode_translate (L : ℝ) [Fact (0 < L)] (n : ℤ) (x s : ℝ) :
    mode L n (x-s) = _root_.fourier n (-(s : AddCircle L))*mode L n x := by
  rw [← AddCircle.coe_neg, _root_.fourier_coe_apply]
  unfold mode omega
  rw [show Complex.I * ((2*Real.pi*(n:ℝ)/L : ℝ) : ℂ) * ((x-s : ℝ) : ℂ) =
    (2*Real.pi*Complex.I*(n:ℂ)*((-s : ℝ) : ℂ)/(L:ℂ)) +
      Complex.I * ((2*Real.pi*(n:ℝ)/L : ℝ) : ℂ) * (x:ℂ) by push_cast; ring]
  rw [Complex.exp_add]
  ring

/-- Mixed periodic energy on Ioc, with all signed, zero and tied indices. -/
theorem periodicPair_formula (L : ℝ) [Fact (0 < L)] (m n : ℤ) (s : ℝ) :
    periodicPair L m n s = if m=n then
      (FormCore.PeriodicSpectralEnergy.phaseGap (d:=L) n s : ℂ) else 0 := by
  rw [periodicPair_eq_mode]
  have hgap (k : ℤ) (x : ℝ) :
      mode L k x-periodicExtension L (-L/2) (mode L k) (x-s) =
        (1-_root_.fourier k (-(s:AddCircle L)))*mode L k x := by
    rw [periodicExtension_mode, mode_translate]
    ring
  simp_rw [hgap]
  have hp := mode_inner L m n
  have hfactor : (∫ x in window L,
      conj ((1-_root_.fourier m (-(s:AddCircle L)))*mode L m x) *
        ((1-_root_.fourier n (-(s:AddCircle L)))*mode L n x)) =
      (conj (1-_root_.fourier m (-(s:AddCircle L))) *
        (1-_root_.fourier n (-(s:AddCircle L)))) *
          (∫ x in window L, conj (mode L m x)*mode L n x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [map_mul]; ring
  rw [hfactor, hp]
  by_cases hmn : m=n
  · subst m
    simp only [ite_true, mul_one]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rfl
  · simp [hmn]

/-- Finite ENNReal-to-Bochner conversion. Positivity prevents zero-times-infinity. -/
lemma finite_scaled_lintegral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (h : X → ℝ) (hm : AEStronglyMeasurable h μ) (hn : 0 ≤ᵐ[μ] h)
    (k A : ℝ) (hk : 0 < k) (hA : 0 ≤ A)
    (he : ENNReal.ofReal A = ENNReal.ofReal k * ∫⁻ x, ENNReal.ofReal (h x) ∂μ) :
    Integrable h μ ∧ A = k * ∫ x, h x ∂μ := by
  have hfin : (∫⁻ x, ENNReal.ofReal (h x) ∂μ) < ∞ := by
    by_contra hnot
    have ht : (∫⁻ x, ENNReal.ofReal (h x) ∂μ) = ∞ := by
      exact top_unique (not_lt.mp hnot)
    rw [ht, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hk))] at he
    exact ENNReal.ofReal_ne_top he
  have hi : Integrable h μ := ⟨hm, (hasFiniteIntegral_iff_ofReal hn).mpr hfin⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal hk.le,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)] using ht

/-- The periodic owner supplies the full scalar increment; no rate truncation. -/
theorem periodic_mixed_integral (L : ℝ) [Fact (0 < L)] (m n : ℤ) :
    IntegrableOn (fun s =>
      (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*periodicPair L m n s)
      (Ioi 0) ∧
    (∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*
      periodicPair L m n s) =
        if m=n then (FormCore.LineFourier.actualIncrement (omega L n) : ℂ) else 0 := by
  have hspec := FormCore.PeriodicSpectralEnergy.actual_gamma_spectralWeight (d:=L) n
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        FormCore.PeriodicSpectralEnergy.phaseGap (d:=L) n s) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (ArchimedeanJumpDecomposition.jump_density_nonnegative hs)
      (sq_nonneg _)
  have hm : AEStronglyMeasurable (fun s =>
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        FormCore.PeriodicSpectralEnergy.phaseGap (d:=L) n s)
      (volume.restrict (Ioi 0)) := by
    unfold ArchimedeanJumpDecomposition.archimedeanJumpDensity
      FormCore.PeriodicSpectralEnergy.phaseGap
    fun_prop
  have he : ENNReal.ofReal (FormCore.LineFourier.actualIncrement (omega L n)) =
      ENNReal.ofReal (1:ℝ) * ∫⁻ s in Ioi 0,
        ENNReal.ofReal (ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
          FormCore.PeriodicSpectralEnergy.phaseGap (d:=L) n s) := by
    rw [ENNReal.ofReal_one, one_mul]
    convert hspec.symm using 1
    · rfl
    · apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact ENNReal.ofReal_mul (ArchimedeanJumpDecomposition.jump_density_nonnegative hs)
  have hi := finite_scaled_lintegral _ _ hm hnn 1
    (FormCore.LineFourier.actualIncrement (omega L n)) (by norm_num)
    (FormCore.LogGraph.actual_gamma_scalar_bounds _).1 he
  simp_rw [periodicPair_formula]
  by_cases hmn : m=n
  · simp only [hmn, ite_true]
    constructor
    · apply (Complex.ofRealCLM.integrable_comp hi.1).congr
      exact Eventually.of_forall fun s => Complex.ofReal_mul _ _
    · simp only [← Complex.ofReal_mul, integral_complex_ofReal]
      exact congrArg Complex.ofReal (by simpa using hi.2.symm)
  · simp [hmn]

/-- Complete periodic rate exchange, paid by the actual finite periodic energy. -/
theorem periodic_complete_rate_interchange (L : ℝ) [Fact (0 < L)] (m n : ℤ) :
    (∀ j : ℕ, IntegrableOn (fun s => (Real.exp (-rate j*s) : ℂ)*periodicPair L m n s)
      (Ioi 0)) ∧
    Summable (fun j : ℕ => ∫ s in Ioi 0, ‖(Real.exp (-rate j*s) : ℂ)*periodicPair L m n s‖) ∧
    (∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s : ℂ)*
      periodicPair L m n s) =
      ∑' j : ℕ, ∫ s in Ioi 0, (Real.exp (-rate j*s) : ℂ)*periodicPair L m n s := by
  apply complete_rate_interchange
  · change AEStronglyMeasurable (fun s : ℝ => periodicPair L m n s)
      (volume.restrict (Ioi 0))
    simp_rw [periodicPair_formula]
    by_cases h : m=n
    · simp only [h,ite_true]
      unfold FormCore.PeriodicSpectralEnergy.phaseGap
      fun_prop
    · simp only [if_neg h]
      exact aestronglyMeasurable_const
  · exact (periodic_mixed_integral L m n).1

end D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation
