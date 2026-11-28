/- GID: D5/S3/MeasureTheory/ExponentialClock
   generality: G
   mirror-B: none(waiver:covered-by-observer-crossed-product-entropy-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A diagonal finite Gibbs weight factors after translation by each energy. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Omega original.

A diagonal finite Gibbs weight factors after translation by each energy.
This gives exponential normalization and change of variables on a half-line.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.MeasureTheory.ExponentialClock

open _root_.MeasureTheory Set
open scoped ENNReal BigOperators

variable {n : Type*} [Fintype n]

/-- The partition function of the Gibbs distribution on the finite energy levels. -/
def partition (β : ℝ) (E : n → ℝ) : ℝ := ∑ i, Real.exp (-β * E i)

/-- The Gibbs probability of the indicated energy eigenvector. -/
def gibbsWeight (β : ℝ) (E : n → ℝ) (i : n) : ℝ :=
  Real.exp (-β * E i) / partition β E

theorem partition_pos [Nonempty n] (β : ℝ) (E : n → ℝ) : 0 < partition β E :=
  Finset.sum_pos (fun i _ => Real.exp_pos (-β * E i)) Finset.univ_nonempty

theorem sum_gibbsWeight [Nonempty n] (β : ℝ) (E : n → ℝ) :
    ∑ i, gibbsWeight β E i = 1 := by
  simp only [gibbsWeight, ← Finset.sum_div]
  change partition β E / partition β E = 1
  exact div_self (partition_pos β E).ne'

/-- Trace weight per matrix degree of freedom in total-energy coordinates. -/
def totalWeight (β : ℝ) (E : n → ℝ) (y : ℝ) : ℝ :=
  β / partition β E * Real.exp (-β * y)

/-- Exponential clock probability density on the positive half-line. -/
def clockWeight (β : ℝ) (x : ℝ) : ℝ := β * Real.exp (-β * x)

theorem totalWeight_pos [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ) (y : ℝ) :
    0 < totalWeight β E y :=
  mul_pos (div_pos hβ (partition_pos β E)) (Real.exp_pos _)

theorem integrableOn_totalWeight [Nonempty n] {β : ℝ} (hβ : 0 < β)
    (E : n → ℝ) (c : ℝ) : IntegrableOn (totalWeight β E) (Ici c) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hβ) c).const_mul _

theorem integral_clockWeight {β : ℝ} (hβ : 0 < β) :
    (∫ x in Ici (0 : ℝ), clockWeight β x) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]
  simp only [clockWeight, integral_const_mul]
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hβ) 0]
  field_simp
  simp

theorem totalWeight_shift (β : ℝ) (E : n → ℝ) (i : n) (x : ℝ) :
    totalWeight β E (x + E i) = gibbsWeight β E i * clockWeight β x := by
  simp only [totalWeight, gibbsWeight, clockWeight, mul_add, Real.exp_add]
  ring

theorem integral_shifted_clock (E : n → ℝ) (β : ℝ) (i : n) (f : ℝ → ℝ) :
    (∫ y in Ici (E i), totalWeight β E y * f (y - E i)) =
      gibbsWeight β E i * ∫ x in Ici (0 : ℝ), clockWeight β x * f x := by
  let shift : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight (E i)
  have hm : Measure.map shift volume = volume := (measurePreserving_add_right volume (E i)).map_eq
  nth_rw 1 [← hm]
  rw [setIntegral_map_equiv]
  have hs : shift ⁻¹' Ici (E i) = Ici 0 := by ext x; simp [shift, MeasurableEquiv.addRight]
  rw [hs, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change totalWeight β E (x + E i) * f (x + E i - E i) = _
  rw [add_sub_cancel_right, totalWeight_shift, mul_assoc]

theorem integrableOn_clock_times {β : ℝ} (hβ : 0 < β) {f : ℝ → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (E : n → ℝ)
    [Nonempty n] (i : n) :
    IntegrableOn (fun y => totalWeight β E y * f (y - E i)) (Ici (E i)) := by
  refine ((integrableOn_totalWeight hβ E (E i)).const_mul C).mono' ?_ ?_
  · exact ((by unfold totalWeight; fun_prop : Measurable (totalWeight β E)).mul (hf.comp (by fun_prop))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (totalWeight_pos hβ E y).le, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (totalWeight_pos hβ E y).le

/-- Move the left endpoint of a half-line integral to zero in each summand. -/
theorem lintegral_shifted_sum (E : n → ℝ) (f : n → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ y, ∑ i, (Ici (E i)).indicator (fun z => f i (z - E i)) y) =
      ∫⁻ x in Ici (0 : ℝ), ∑ i, f i x := by
  have ht (i : n) : (∫⁻ y, (Ici (E i)).indicator (fun z => f i (z - E i)) y) =
      ∫⁻ x in Ici (0 : ℝ), f i x := by
    let shift : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight (E i)
    rw [MeasurePreserving.lintegral_map_equiv _ shift (measurePreserving_add_right volume (E i)),
      ← lintegral_indicator measurableSet_Ici]
    apply lintegral_congr
    intro x
    change (Ici (E i)).indicator (fun z => f i (z - E i)) (x + E i) =
      (Ici (0 : ℝ)).indicator (f i) x
    have he : E i ≤ x + E i ↔ 0 ≤ x := by
      constructor <;> intro h <;> linarith
    simp [Set.indicator, he]
  have hf' (i : n) : Measurable ((Ici (E i)).indicator (fun z => f i (z - E i))) :=
    ((hf i).comp (show Measurable (fun z : ℝ => z - E i) by fun_prop)).indicator measurableSet_Ici
  rw [lintegral_finsetSum _ (fun i _ => hf' i)]
  simp_rw [ht]
  exact (lintegral_finsetSum _ (fun i _ => hf i)).symm

/-- A strictly positive weight detects the same zero sets as the integrand. -/
theorem lintegral_ofReal_weighted_eq_zero_iff {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w f : X → ℝ} (hw : Measurable w) (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ, 0 < w x) (hn : 0 ≤ᵐ[μ] f) :
    (∫⁻ x, ENNReal.ofReal (w x * f x) ∂μ) = 0 ↔ f =ᵐ[μ] 0 := by
  have hm : Measurable (fun x => ENNReal.ofReal (w x * f x)) := (hw.mul hf).ennreal_ofReal
  rw [lintegral_eq_zero_iff hm]
  constructor
  · intro h
    filter_upwards [h, hpos, hn] with x hx hp hx₀
    exact le_antisymm (nonpos_of_mul_nonpos_right (ENNReal.ofReal_eq_zero.mp hx) hp) hx₀
  · intro h
    exact h.mono fun x hx => by simp [show f x = 0 from hx]

/-- A nonnegative integrable gap obtained by subtracting and adding terms of equal
integral has the same extended integral as the remaining term. -/
theorem neg_lintegral_gap_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g j k : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hj : Integrable j μ)
    (hn : (∫ x, g x ∂μ) = ∫ x, j x ∂μ) (hk : k =ᵐ[μ] fun x => f x - g x + j x)
    (hkn : 0 ≤ᵐ[μ] k) :
    -(↑(∫⁻ x, ENNReal.ofReal (k x) ∂μ) : EReal) = (-(∫ x, f x ∂μ) : ℝ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((hf.sub hg).add hj |>.congr hk.symm) hkn,
    EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast integral_nonneg_of_ae hkn),
    ← EReal.coe_neg, integral_congr_ae hk]
  have he : (∫ x, f x - g x + j x ∂μ) = ∫ x, f x ∂μ := calc
    _ = (∫ x, f x - g x ∂μ) + ∫ x, j x ∂μ := integral_add (hf.sub hg) hj
    _ = (∫ x, f x ∂μ) - (∫ x, j x ∂μ) + (∫ x, j x ∂μ) := by rw [integral_sub hf hg, hn]
    _ = _ := sub_add_cancel _ _
  exact congrArg (fun r : ℝ => ((-r : ℝ) : EReal)) he


/-- Integrate a finite weighted sum of translated diagonal contributions by
integrating each term on its physical clock half-line. -/
theorem integral_shifted_sum (E : n → ℝ) (β : ℝ) (f : n → ℝ → ℝ)
    (hf : ∀ i, IntegrableOn (fun x => clockWeight β x * f i x) (Ici 0)) :
    let g := fun y => ∑ i, (Ici (E i)).indicator
      (fun z => totalWeight β E z * f i (z - E i)) y
    Integrable g ∧ (∫ y, g y) =
      ∫ x in Ici 0, ∑ i, gibbsWeight β E i * (clockWeight β x * f i x) := by
  let d (i : n) (y : ℝ) := totalWeight β E y * f i (y - E i)
  have hd (i : n) : Integrable ((Ici (E i)).indicator (d i)) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ici
    let shift : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight (E i)
    have hm := measurePreserving_add_right volume (E i)
    have hs : shift ⁻¹' Ici (E i) = Ici 0 := by ext x; simp [shift, MeasurableEquiv.addRight]
    apply (hm.integrableOn_comp_preimage shift.measurableEmbedding).mp
    change IntegrableOn _ (shift ⁻¹' Ici (E i))
    rw [hs]
    refine ((hf i).const_mul (gibbsWeight β E i)).congr (Filter.Eventually.of_forall fun x => ?_)
    change _ = totalWeight β E (x + E i) * f i (x + E i - E i)
    rw [add_sub_cancel_right, totalWeight_shift, mul_assoc]
  dsimp only
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hd i), ?_⟩
  change (∫ y, ∑ i, (Ici (E i)).indicator (d i) y) = _
  rw [integral_finsetSum _ (fun i _ => hd i),
    integral_finsetSum _ (fun i _ => (hf i).const_mul (gibbsWeight β E i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator measurableSet_Ici, show d i = _ by rfl, integral_shifted_clock,
    integral_const_mul]


theorem log_clock_mul {β : ℝ} (hβ : 0 < β) (x p : ℝ) :
    p * Real.log (p / clockWeight β x) = p * Real.log p + p * (β * x) - Real.log β * p := by
  by_cases hz : p = 0
  · simp [hz]
  rw [clockWeight, Real.log_div hz (mul_ne_zero hβ.ne' (Real.exp_ne_zero _)),
    Real.log_mul hβ.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem finite_clock_log {β : ℝ} (hβ : 0 < β) {p : ℝ → ℝ}
    (hp : Measurable p) (hn : ∀ x, 0 ≤ p x)
    (hp1 : ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (p x) = 1)
    (hpl : IntegrableOn (fun x => p x * Real.log (p x)) (Ici 0))
    (hxp : IntegrableOn (fun x => x * p x) (Ici 0)) :
    IntegrableOn p (Ici 0) ∧ (∫ x in Ici (0 : ℝ), p x) = 1 ∧
      IntegrableOn (fun x => p x * Real.log (p x / clockWeight β x)) (Ici 0) := by
  have hpos : 0 ≤ᵐ[volume.restrict (Ici (0 : ℝ))] p := Filter.Eventually.of_forall hn
  have hi : IntegrableOn p (Ici 0) :=
    (lintegral_ofReal_ne_top_iff_integrable hp.aestronglyMeasurable hpos).mp
      (hp1.symm ▸ ENNReal.one_ne_top)
  refine ⟨hi, ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae hpos hi.1, hp1, ENNReal.toReal_one]
  · refine ((hpl.add (hxp.const_mul β)).sub (hi.const_mul (Real.log β))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, log_clock_mul hβ]
    ring

/-- Expanding the reference clock logarithm fixes the additive constant. -/
theorem negative_clock_relative_entropy_split {β : ℝ} (hβ : 0 < β)
    (p d : ℝ → ℝ) (hp : IntegrableOn p (Ici 0)) (hm : (∫ x in Ici (0 : ℝ), p x) = 1)
    (hpl : IntegrableOn (fun x => p x * Real.log (p x)) (Ici 0))
    (hpm : IntegrableOn (fun x => p x * (β * x + d x)) (Ici 0)) :
    -(∫ x in Ici (0 : ℝ), p x * (Real.log (p x / clockWeight β x) + d x)) =
      -(∫ x in Ici (0 : ℝ), p x * (β * x + d x)) -
        (∫ x in Ici (0 : ℝ), p x * Real.log (p x)) + Real.log β := by
  have h (x : ℝ) : p x * (Real.log (p x / clockWeight β x) + d x) =
      p x * Real.log (p x) + p x * (β * x + d x) - Real.log β * p x := by
    rw [mul_add, log_clock_mul hβ]
    ring
  have hs : IntegrableOn (fun x => p x * Real.log (p x) + p x * (β * x + d x)) (Ici 0) :=
    hpl.add hpm
  simp only [h]
  rw [integral_sub hs (hp.const_mul _), integral_add hpl hpm, integral_const_mul, hm]
  ring

end Omega.MeasureTheory.ExponentialClock
