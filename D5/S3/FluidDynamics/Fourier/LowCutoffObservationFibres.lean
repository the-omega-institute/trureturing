/- GID: D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Fourier/LowCutoffObservationFibres
   mirror-E: none(waiver:exact-symbolic-Fourier-family)
   anchors: []
   utility: none
   digest: Every instantaneous datum inside the unit frequency cutoff is a function of the pair alpha and alpha times beta. -/

import D5.S3.FluidDynamics.Fourier.AugmentedReadoutRecovery
import Mathlib.Tactic.IntervalCases

/-!
# The fibres of the low-cutoff instantaneous datum

The low observation together with every acceleration component at every mode of
squared frequency at most one is a function of the pair `(alpha, alpha * beta)`,
and that pair is recoverable from it. So the observation model cannot separate
two parameter pairs with the same `alpha` and the same product, and inverting
for `beta` is division by `alpha`.

The cutoff boundary is sharp in a specific sense: the hidden wave sits at
frequency `(-1, 1)`, whose squared frequency is two, and the viscous term there
carries `beta` linearly. The obstruction is therefore a property of the cutoff
on this family, not a statement that no observation recovers `beta`.

This concerns one explicit two-parameter family and instantaneous data. It is
not general Navier-Stokes observability, not recovery from finite-time
histories, and it asserts nothing about existence or blowup.

Every declaration quantifies over continuous real parameters, so none of the
four computational classes applies: there is no bounded enumeration, no checker,
no numeric reduction and no certified finite instance. The refutation below
proceeds by an explicit real-parameter family rather than a finite computation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.LowCutoffObservationFibres

open LowModeReversalWitness
open D5.S3.FluidDynamics.Fourier.AugmentedReadoutRecovery

/-- The complete instantaneous datum visible inside the squared-frequency cutoff. -/
def lowCutoffDatum (nu alpha beta : ℝ) : (Mode → Amplitude) × (Mode → Amplitude) :=
  (lowObservation alpha beta,
    fun k c => if frequencySquared k ≤ 1 then acceleration nu alpha beta k c else 0)

private lemma cutoff_modes (k : Mode) (hk : frequencySquared k ≤ 1) :
    k = (0, 0) ∨ k = (1, 0) ∨ k = (-1, 0) ∨ k = (0, 1) ∨ k = (0, -1) := by
  obtain ⟨a, b⟩ := k
  have hk' : a ^ 2 + b ^ 2 ≤ 1 := hk
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg a, sq_nonneg (b + 1)]
  have hb2 : b ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg (b - 1)]
  clear hk
  interval_cases a <;> interval_cases b <;> revert hk' <;> norm_num [Prod.ext_iff]

private lemma accel_origin (nu alpha beta : ℝ) (c : Fin 3) :
    acceleration nu alpha beta (0, 0) c = 0 := by
  fin_cases c <;>
    simp only [acceleration, coefficient, leray, advection, Fin.sum_univ_four] <;>
    norm_num [frequencySquared, frequency, inputAmplitude, Prod.mk_add_mk,
      Prod.mk.injEq, Fin.ext_iff]

private lemma accel_up (nu alpha beta : ℝ) (c : Fin 3) :
    acceleration nu alpha beta (0, 1) c =
      if c = 0 then -Complex.I * (alpha : ℂ) * (beta : ℂ) / 4 else 0 := by
  fin_cases c <;>
    simp only [acceleration, coefficient, leray, advection, Fin.sum_univ_four] <;>
    norm_num [frequencySquared, frequency, inputAmplitude, Prod.mk_add_mk,
      Prod.mk.injEq, Fin.ext_iff] <;> ring

private lemma accel_down (nu alpha beta : ℝ) (c : Fin 3) :
    acceleration nu alpha beta (0, -1) c =
      if c = 0 then Complex.I * (alpha : ℂ) * (beta : ℂ) / 4 else 0 := by
  fin_cases c <;>
    simp only [acceleration, coefficient, leray, advection, Fin.sum_univ_four] <;>
    norm_num [frequencySquared, frequency, inputAmplitude, Prod.mk_add_mk,
      Prod.mk.injEq, Fin.ext_iff] <;> ring

private lemma accel_right (nu alpha beta : ℝ) (c : Fin 3) :
    acceleration nu alpha beta (1, 0) c =
      if c = 1 then -(nu : ℂ) * (alpha : ℂ) / 2 else 0 := by
  fin_cases c <;>
    simp only [acceleration, coefficient, leray, advection, Fin.sum_univ_four] <;>
    norm_num [frequencySquared, frequency, inputAmplitude, Prod.mk_add_mk,
      Prod.mk.injEq, Fin.ext_iff] <;> ring

private lemma accel_left (nu alpha beta : ℝ) (c : Fin 3) :
    acceleration nu alpha beta (-1, 0) c =
      if c = 1 then -(nu : ℂ) * (alpha : ℂ) / 2 else 0 := by
  fin_cases c <;>
    simp only [acceleration, coefficient, leray, advection, Fin.sum_univ_four] <;>
    norm_num [frequencySquared, frequency, inputAmplitude, Prod.mk_add_mk,
      Prod.mk.injEq, Fin.ext_iff] <;> ring

/-- Inside the cutoff every acceleration component depends on the amplitudes only
through `alpha` and the product `alpha * beta`. -/
private lemma accel_cutoff_congr (nu alpha beta alpha' beta' : ℝ)
    (ha : alpha = alpha') (hp : alpha * beta = alpha' * beta')
    (k : Mode) (hk : frequencySquared k ≤ 1) (c : Fin 3) :
    acceleration nu alpha beta k c = acceleration nu alpha' beta' k c := by
  have hpc : ((alpha : ℂ)) * (beta : ℂ) = ((alpha' : ℂ)) * (beta' : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hp
  rcases cutoff_modes k hk with h | h | h | h | h <;> subst h
  · rw [accel_origin, accel_origin]
  · rw [accel_right, accel_right, ha]
  · rw [accel_left, accel_left, ha]
  · rw [accel_up, accel_up]
    by_cases hc : c = 0
    · simp only [hc]
      rw [mul_assoc, mul_assoc, hpc]
    · simp only [if_neg hc]
  · rw [accel_down, accel_down]
    by_cases hc : c = 0
    · simp only [hc]
      rw [mul_assoc, mul_assoc, hpc]
    · simp only [if_neg hc]

private lemma cutoff_up : frequencySquared ((0 : ℤ), (1 : ℤ)) ≤ 1 := by
  norm_num [frequencySquared]

/-- The fibres of the low-cutoff datum are exactly the level sets of the pair
`(alpha, alpha * beta)`. -/
theorem lowCutoffDatum_eq_iff (nu alpha beta alpha' beta' : ℝ) :
    lowCutoffDatum nu alpha beta = lowCutoffDatum nu alpha' beta' ↔
      alpha = alpha' ∧ alpha * beta = alpha' * beta' := by
  constructor
  · intro h
    have h1 : lowObservation alpha beta (1, 0) 1 = lowObservation alpha' beta' (1, 0) 1 :=
      congrFun (congrFun (congrArg Prod.fst h) (1, 0)) 1
    rw [low_observation_visible, low_observation_visible] at h1
    have ha : alpha = alpha' := by
      have := congrArg Complex.re h1
      simpa using this
    have h2 : (if frequencySquared ((0 : ℤ), (1 : ℤ)) ≤ 1 then
          acceleration nu alpha beta (0, 1) 0 else 0) =
        (if frequencySquared ((0 : ℤ), (1 : ℤ)) ≤ 1 then
          acceleration nu alpha' beta' (0, 1) 0 else 0) :=
      congrFun (congrFun (congrArg Prod.snd h) (0, 1)) 0
    rw [if_pos cutoff_up, if_pos cutoff_up, transverse_acceleration,
      transverse_acceleration] at h2
    have h3 := congrArg Complex.im h2
    simp [Complex.ext_iff] at h3
    refine ⟨ha, ?_⟩
    linarith
  · rintro ⟨ha, hp⟩
    apply Prod.ext
    · show lowObservation alpha beta = lowObservation alpha' beta'
      rw [← ha]
      exact lowObservation_independent alpha beta beta'
    · funext k c
      show (if frequencySquared k ≤ 1 then acceleration nu alpha beta k c else 0) =
        (if frequencySquared k ≤ 1 then acceleration nu alpha' beta' k c else 0)
      by_cases hk : frequencySquared k ≤ 1
      · rw [if_pos hk, if_pos hk, accel_cutoff_congr nu alpha beta alpha' beta' ha hp k hk c]
      · rw [if_neg hk, if_neg hk]

/-- A real-valued gap on the low-cutoff datum, built from the visible amplitude
slot and the transverse acceleration slot. -/
def cutoffGap (nu alpha beta alpha' beta' : ℝ) : ℝ :=
  ‖lowObservation alpha beta (1, 0) 1 - lowObservation alpha' beta' (1, 0) 1‖ +
    ‖acceleration nu alpha beta (0, 1) 0 - acceleration nu alpha' beta' (0, 1) 0‖

private lemma norm_real_mul_I (r : ℝ) : ‖((r : ℝ) : ℂ) * Complex.I‖ = |r| := by
  simp

private lemma cutoffGap_formula (nu alpha beta alpha' beta' : ℝ) :
    cutoffGap nu alpha beta alpha' beta' =
      |alpha - alpha'| / 2 + |alpha * beta - alpha' * beta'| / 4 := by
  have h1 : lowObservation alpha beta (1, 0) 1 - lowObservation alpha' beta' (1, 0) 1
      = (((alpha - alpha') / 2 : ℝ) : ℂ) := by
    rw [low_observation_visible, low_observation_visible]
    push_cast
    ring
  have h2 : acceleration nu alpha beta (0, 1) 0 - acceleration nu alpha' beta' (0, 1) 0
      = ((-(alpha * beta - alpha' * beta') / 4 : ℝ) : ℂ) * Complex.I := by
    rw [transverse_acceleration, transverse_acceleration]
    push_cast
    ring
  rw [cutoffGap, h1, h2, Complex.norm_real, Real.norm_eq_abs, norm_real_mul_I,
    abs_div, abs_div, abs_neg]
  norm_num

/-- The gap vanishes exactly on the fibres. -/
theorem cutoffGap_eq_zero_iff (nu alpha beta alpha' beta' : ℝ) :
    cutoffGap nu alpha beta alpha' beta' = 0 ↔
      lowCutoffDatum nu alpha beta = lowCutoffDatum nu alpha' beta' := by
  rw [cutoffGap_formula, lowCutoffDatum_eq_iff]
  constructor
  · intro h
    have h1 : |alpha - alpha'| = 0 := by
      nlinarith [abs_nonneg (alpha - alpha'), abs_nonneg (alpha * beta - alpha' * beta')]
    have h2 : |alpha * beta - alpha' * beta'| = 0 := by
      nlinarith [abs_nonneg (alpha - alpha'), abs_nonneg (alpha * beta - alpha' * beta')]
    exact ⟨by linarith [abs_eq_zero.mp h1], by linarith [abs_eq_zero.mp h2]⟩
  · rintro ⟨ha, hp⟩
    rw [hp, ha]
    simp

/-- The claim that `beta` is recoverable from the low-cutoff datum with a modulus
of continuity uniform over the whole family. -/
def UniformlyStableCutoffBetaRecovery (nu : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ alpha beta alpha' beta' : ℝ,
    cutoffGap nu alpha beta alpha' beta' < δ → |beta - beta'| < ε

/-- No uniform modulus exists: shrinking `alpha` makes the gap arbitrarily small
while `beta` stays a fixed distance apart. -/
theorem not_uniformlyStableCutoffBetaRecovery (nu : ℝ) :
    ¬ UniformlyStableCutoffBetaRecovery nu := by
  intro H
  obtain ⟨δ, hδ, hbound⟩ := H 1 zero_lt_one
  have ha : 0 < min δ 1 := lt_min hδ zero_lt_one
  have hle : min δ 1 ≤ δ := min_le_left _ _
  have hg : cutoffGap nu (min δ 1) 0 (min δ 1) 2 < δ := by
    rw [cutoffGap_formula]
    have e1 : min δ 1 - min δ 1 = 0 := by ring
    have e2 : min δ 1 * 0 - min δ 1 * 2 = -(2 * min δ 1) := by ring
    rw [e1, e2, abs_zero, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * min δ 1)]
    linarith
  have hcon := hbound (min δ 1) 0 (min δ 1) 2 hg
  norm_num at hcon

/-- On the slab where the visible amplitude is at least `a`, recovery of `beta` is
Lipschitz with constant `4 / a`. -/
theorem cutoff_beta_modulus_on_slab (nu a alpha beta beta' : ℝ) (ha : 0 < a)
    (halpha : a ≤ |alpha|) :
    |beta - beta'| ≤ 4 / a * cutoffGap nu alpha beta alpha beta' := by
  rw [cutoffGap_formula]
  have e1 : alpha - alpha = 0 := by ring
  have e2 : alpha * beta - alpha * beta' = alpha * (beta - beta') := by ring
  rw [e1, e2, abs_zero, abs_mul]
  have hb : 0 ≤ |beta - beta'| := abs_nonneg _
  have key : a * |beta - beta'| ≤ |alpha| * |beta - beta'| :=
    mul_le_mul_of_nonneg_right halpha hb
  have hexp : 4 / a * (0 / 2 + |alpha| * |beta - beta'| / 4)
      = |alpha| * |beta - beta'| / a := by
    field_simp
    ring
  rw [hexp, le_div_iff₀ ha]
  nlinarith [key]

/-- The slab constant `4 / a` is attained, so it cannot be improved. -/
theorem cutoff_beta_modulus_on_slab_sharp (nu a : ℝ) (ha : 0 < a) (c : ℝ)
    (hc : c < 4 / a) :
    ∃ alpha beta beta' : ℝ, a ≤ |alpha| ∧
      c * cutoffGap nu alpha beta alpha beta' < |beta - beta'| := by
  refine ⟨a, 0, 1, le_of_eq (abs_of_pos ha).symm, ?_⟩
  rw [cutoffGap_formula]
  have e1 : a - a = 0 := by ring
  have e2 : a * 0 - a * 1 = -a := by ring
  have e3 : (0 : ℝ) - 1 = -1 := by ring
  rw [e1, e2, e3, abs_zero, abs_neg, abs_of_pos ha, abs_neg, abs_one]
  have h4 : 4 / a * a = 4 := by field_simp
  have hlt : c * a < 4 := by
    have h := mul_lt_mul_of_pos_right hc ha
    rwa [h4] at h
  have e4 : c * (0 / 2 + a / 4) = c * a / 4 := by ring
  rw [e4]
  linarith

#print axioms lowCutoffDatum_eq_iff
#print axioms cutoffGap_eq_zero_iff
#print axioms not_uniformlyStableCutoffBetaRecovery
#print axioms cutoff_beta_modulus_on_slab
#print axioms cutoff_beta_modulus_on_slab_sharp

end D5.S3.FluidDynamics.Fourier.LowCutoffObservationFibres
