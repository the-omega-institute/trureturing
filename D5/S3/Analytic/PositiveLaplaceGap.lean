/- GID: D5/S3/Analytic/PositiveLaplaceGap
   generality: G
   mirror-B: D5/B/S3/Analytic/PositiveLaplaceGap
   mirror-E: none(waiver:exact-positive-measure-inequalities)
   anchors: []
   utility: none
   digest: Actual positive Laplace integrals bound low-energy mass, with a sharp half-gap noise floor. -/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Positive Laplace observations and low-energy mass

The measure is a genuine finite positive measure on nonnegative energies.
Integrability and the low-energy lower bound are proved, rather than supplied
as abstract correlation/spectral-mass hypotheses. The principal finite-noise
bound is a direct consumer of Mathlib's Markov integral inequality.

The half-gap estimate is sharp for the stated class of finite measures;
it is not asserted to be sharp after prescribing total mass one. No
Hamiltonian, quantum field theory, or Yang--Mills identification is asserted.

Source scope: the uploaded Axabra Yang--Mills proof file motivates the missing
positive-measure bridge. The proofs here use Mathlib's integral API and the
ordinary arguments in Section 13 of NS_OBSERVER_DYNAMICS_RH_THEORY.md.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.PositiveLaplaceGap

open MeasureTheory Set
open scoped NNReal

/-- The actual Laplace integral of a positive energy measure. -/
def laplaceCorrelation (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ E, Real.exp (-t * (E : ℝ)) ∂μ

private theorem kernel_integrable (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun E : ℝ≥0 => Real.exp (-t * (E : ℝ))) μ := by
  have hc : Continuous (fun E : ℝ≥0 => Real.exp (-t * (E : ℝ))) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun E => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) E.property)

private theorem low_mass_lower (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (r : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) :
    μ.real (Iic r) * Real.exp (-t * (r : ℝ)) ≤ laplaceCorrelation μ t := by
  have hsub : Iic r ⊆
      {E : ℝ≥0 | Real.exp (-t * (r : ℝ)) ≤ Real.exp (-t * (E : ℝ))} := by
    intro E hE
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (show (E : ℝ) ≤ (r : ℝ) from hE) (neg_nonpos.mpr ht)
  have hmono := mul_le_mul_of_nonneg_left
    (measureReal_mono (μ := μ) hsub) (Real.exp_pos (-t * (r : ℝ))).le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun E : ℝ≥0 => Real.exp (-t * (E : ℝ)))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (kernel_integrable μ t ht) (Real.exp (-t * (r : ℝ)))
  simpa only [laplaceCorrelation, mul_comm] using hmono.trans hmarkov

/-- A one-time, one-sided envelope bounds the actual low-energy mass.
The additive error is amplified by exp(r*t); no exact gap is inferred. -/
theorem low_energy_mass_le (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (r : ℝ≥0) (Δ K ε t : ℝ) (ht : 0 ≤ t)
    (hobs : laplaceCorrelation μ t ≤ K * Real.exp (-Δ * t) + ε) :
    μ.real (Iic r) ≤
      K * Real.exp (-(Δ - (r : ℝ)) * t) + ε * Real.exp ((r : ℝ) * t) := by
  have hlow := (low_mass_lower μ r t ht).trans hobs
  calc
    μ.real (Iic r) =
        (μ.real (Iic r) * Real.exp (-t * (r : ℝ))) *
          Real.exp ((r : ℝ) * t) := by
      rw [mul_assoc, ← Real.exp_add]
      have hz : -t * (r : ℝ) + (r : ℝ) * t = 0 := by ring
      rw [hz, Real.exp_zero, mul_one]
    _ ≤ (K * Real.exp (-Δ * t) + ε) * Real.exp ((r : ℝ) * t) :=
      mul_le_mul_of_nonneg_right hlow (Real.exp_pos _).le
    _ = K * Real.exp (-(Δ - (r : ℝ)) * t) +
        ε * Real.exp ((r : ℝ) * t) := by
      have harg : -Δ * t + (r : ℝ) * t = -(Δ - (r : ℝ)) * t := by ring
      rw [add_mul, mul_assoc, ← Real.exp_add, harg]

/-- Noiseless all-time exponential decay removes every strictly subthreshold
closed energy interval of the genuine measure. -/
theorem subthreshold_mass_eq_zero (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (r : ℝ≥0) (Δ K : ℝ) (hK : 0 ≤ K) (hr : (r : ℝ) < Δ)
    (hdecay : ∀ t : ℝ, 0 ≤ t →
      laplaceCorrelation μ t ≤ K * Real.exp (-Δ * t)) :
    μ (Iic r) = 0 := by
  have hnonneg : 0 ≤ μ.real (Iic r) := ENNReal.toReal_nonneg
  have hzero : μ.real (Iic r) = 0 := by
    by_contra hne
    have ha : 0 < μ.real (Iic r) := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have ha0 : μ.real (Iic r) ≠ 0 := ne_of_gt ha
    let δ : ℝ := Δ - (r : ℝ)
    have hδ : 0 < δ := sub_pos.mpr hr
    let T : ℝ := (K / μ.real (Iic r) + 1) / δ
    have hT : 0 ≤ T := div_nonneg (by positivity) hδ.le
    have hb := low_energy_mass_le μ r Δ K 0 T hT (by simpa using hdecay T hT)
    have hbound : μ.real (Iic r) * Real.exp (δ * T) ≤ K := by
      have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (δ * T)).le
      have hcancel : -(Δ - (r : ℝ)) * T + δ * T = 0 := by
        dsimp [δ]
        ring
      simpa only [zero_mul, add_zero, mul_assoc, ← Real.exp_add,
        hcancel, Real.exp_zero, mul_one] using hm
    have hexp : 1 + δ * T ≤ Real.exp (δ * T) := by
      simpa only [add_comm] using Real.add_one_le_exp (δ * T)
    have hlin := (mul_le_mul_of_nonneg_left hexp hnonneg).trans hbound
    have hδT : δ * T = K / μ.real (Iic r) + 1 := by
      dsimp [T]
      field_simp [ne_of_gt hδ] <;> ring
    rw [hδT] at hlin
    have halgebra : μ.real (Iic r) * (1 + (K / μ.real (Iic r) + 1)) =
        K + 2 * μ.real (Iic r) := by
      field_simp [ha0]
      <;> ring
    rw [halgebra] at hlin
    linarith
  exact (measureReal_eq_zero_iff (measure_ne_top μ (Iic r))).mp hzero

/-- The exact optimized half-gap bound. With K=a^2 and error=b^2,
the best possible universal mass bound at energy r is 2*a*b when 0<b<=a.
The proof uses the actual observation time log(a/b)/r. -/
theorem sharp_half_gap_upper (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (r : ℝ≥0) (hr : 0 < (r : ℝ)) (a b : ℝ)
    (hb : 0 < b) (hba : b ≤ a)
    (hobs : ∀ t : ℝ, 0 ≤ t → laplaceCorrelation μ t ≤
      a ^ 2 * Real.exp (-(2 * (r : ℝ)) * t) + b ^ 2) :
    μ.real (Iic r) ≤ 2 * a * b := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  let T : ℝ := Real.log (a / b) / (r : ℝ)
  have hratio : 1 ≤ a / b := (le_div_iff₀ hb).mpr (by simpa using hba)
  have hT : 0 ≤ T := div_nonneg (Real.log_nonneg hratio) hr.le
  have hrt : (r : ℝ) * T = Real.log (a / b) := by
    dsimp [T]
    field_simp [hr0] <;> ring
  have hexp : Real.exp ((r : ℝ) * T) = a / b := by
    rw [hrt, Real.exp_log (div_pos ha hb)]
  have hexpneg : Real.exp (-(2 * (r : ℝ) - (r : ℝ)) * T) = (a / b)⁻¹ := by
    have harg : -(2 * (r : ℝ) - (r : ℝ)) * T = -((r : ℝ) * T) := by ring
    rw [harg, Real.exp_neg, hexp]
  have hm := low_energy_mass_le μ r (2 * (r : ℝ)) (a ^ 2) (b ^ 2) T hT (hobs T hT)
  rw [hexpneg, hexp] at hm
  have halgebra : a ^ 2 * (a / b)⁻¹ + b ^ 2 * (a / b) = 2 * a * b := by
    field_simp [ha0, hb0]
    <;> ring
  rwa [halgebra] at hm

/-- Exact evaluation for a positive atomic measure, used to exhibit extremizers. -/
theorem laplace_smul_dirac (w E : ℝ≥0) (t : ℝ) :
    laplaceCorrelation (w • Measure.dirac E) t =
      (w : ℝ) * Real.exp (-t * (E : ℝ)) := by
  simp [laplaceCorrelation, integral_smul_nnreal_measure, NNReal.smul_def]

/-- Exact feasibility reduction for any family of nonnegative-time upper bounds.
A prescribed low-energy mass is feasible if and only if concentrating that mass
at the threshold is feasible. Arbitrary positive measures cannot improve it. -/
theorem low_mass_feasible_iff_single_atom (r m : ℝ≥0)
    (times : Set ℝ) (U : ℝ → ℝ) (htimes : ∀ t ∈ times, 0 ≤ t) :
    (∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      μ.real (Iic r) = (m : ℝ) ∧
      ∀ t ∈ times, laplaceCorrelation μ t ≤ U t) ↔
    (∀ t ∈ times, (m : ℝ) * Real.exp (-t * (r : ℝ)) ≤ U t) := by
  constructor
  · rintro ⟨μ, hfinite, hmass, hbound⟩
    letI : IsFiniteMeasure μ := hfinite
    intro t ht
    rw [← hmass]
    exact (low_mass_lower μ r t (htimes t ht)).trans (hbound t ht)
  · intro h
    refine ⟨m • Measure.dirac r, inferInstance, ?_, ?_⟩
    · simp [measureReal_nnreal_smul_apply, measureReal_def,
        Measure.dirac_apply, measurableSet_Iic]
    · intro t ht
      simpa only [laplace_smul_dirac] using h t ht

/-- The upper bound 2*a*b is attained in the class of finite positive measures.
The envelope follows from (a*exp(-r*t)-b)^2 >= 0 at every real time. -/
theorem half_gap_extremizer (a b r : ℝ≥0) :
    let μ : Measure ℝ≥0 := (2 * a * b) • Measure.dirac r
    μ.real (Iic r) = 2 * (a : ℝ) * (b : ℝ) ∧
      ∀ t : ℝ, laplaceCorrelation μ t ≤
        (a : ℝ) ^ 2 * Real.exp (-(2 * (r : ℝ)) * t) + (b : ℝ) ^ 2 := by
  dsimp only
  constructor
  · simp [measureReal_nnreal_smul_apply, measureReal_def,
      Measure.dirac_apply, measurableSet_Iic]
  · intro t
    rw [laplace_smul_dirac]
    have hs : Real.exp (-(2 * (r : ℝ)) * t) =
        Real.exp (-t * (r : ℝ)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hs]
    push_cast
    nlinarith [sq_nonneg ((a : ℝ) * Real.exp (-t * (r : ℝ)) - (b : ℝ))]

#print axioms laplaceCorrelation
#print axioms laplace_smul_dirac
#print axioms low_energy_mass_le
#print axioms subthreshold_mass_eq_zero
#print axioms sharp_half_gap_upper
#print axioms low_mass_feasible_iff_single_atom
#print axioms half_gap_extremizer

end D5.S3.Analytic.PositiveLaplaceGap
