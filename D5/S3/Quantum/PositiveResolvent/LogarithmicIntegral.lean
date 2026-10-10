/- GID: D5/S3/Quantum/PositiveResolvent/LogarithmicIntegral
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluate the logarithmic master integral and normalized density by strip residues and exponential substitution. -/

import D5.S3.Quantum.PositiveResolvent.MasterStripLimits
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

open Set MeasureTheory
namespace D5.S3.Quantum.PositiveResolvent.LogarithmicIntegral

open D5.S3.Quantum.PositiveResolvent.MasterStripLimits

noncomputable def masterValue (x : ℝ) : ℝ :=
  if x = 1 then 1 / 2 else 1 / Real.log x - 1 / (x - 1)

private lemma scaled_exp_image (u : ℝ) (hu : 0 < u) :
    (fun s : ℝ => u * Real.exp s) '' Set.univ = Set.Ioi 0 := by
  ext t
  constructor
  · rintro ⟨s, _, rfl⟩
    exact mul_pos hu (Real.exp_pos s)
  · intro ht
    have htpos : t / u ∈ Set.range Real.exp := by
      rw [Real.range_exp]
      exact div_pos ht hu
    obtain ⟨s, hs⟩ := htpos
    refine ⟨s, Set.mem_univ _, ?_⟩
    change u * Real.exp s = t
    rw [hs]
    field_simp [hu.ne']

private lemma scaled_exp_integral (u : ℝ) (hu : 0 < u) (g : ℝ → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), g t) = ∫ s : ℝ, (u * Real.exp s) * g (u * Real.exp s) := by
  rw [← scaled_exp_image u hu]
  simpa only [abs_of_pos (mul_pos hu (Real.exp_pos _)), smul_eq_mul,
    MeasureTheory.setIntegral_univ] using
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (f := fun s : ℝ => u * Real.exp s) (f' := fun s => u * Real.exp s)
      MeasurableSet.univ (fun s _ => ((Real.hasDerivAt_exp s).const_mul u).hasDerivWithinAt)
      (fun a _ b _ hab => Real.exp_injective (mul_left_cancel₀ hu.ne' hab)) g

private lemma scaled_exp_integrable_iff (u : ℝ) (hu : 0 < u) (g : ℝ → ℝ) :
    IntegrableOn g (Set.Ioi 0) ↔
      Integrable (fun s : ℝ => (u * Real.exp s) * g (u * Real.exp s)) := by
  rw [← scaled_exp_image u hu]
  simpa only [abs_of_pos (mul_pos hu (Real.exp_pos _)), smul_eq_mul,
    MeasureTheory.integrableOn_univ] using
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (f := fun s : ℝ => u * Real.exp s) (f' := fun s => u * Real.exp s)
      MeasurableSet.univ (fun s _ => ((Real.hasDerivAt_exp s).const_mul u).hasDerivWithinAt)
      (fun a _ b _ hab => Real.exp_injective (mul_left_cancel₀ hu.ne' hab)) g

theorem logarithmic_density_mass (u : ℝ) (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => 1 / (t * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2))) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), 1 / (t * ((Real.log (t / u)) ^ 2 + Real.pi ^ 2))) = 1 := by
  have heq : (fun s : ℝ => (u * Real.exp s) *
      (1 / ((u * Real.exp s) * ((Real.log (u * Real.exp s / u)) ^ 2 + Real.pi ^ 2)))) =
      (fun s : ℝ => 1 / (s ^ 2 + Real.pi ^ 2)) := by
    funext s
    rw [mul_div_cancel_left₀ _ hu.ne', Real.log_exp]
    field_simp [hu.ne', Real.exp_ne_zero]
  constructor
  · apply (scaled_exp_integrable_iff u hu _).mpr
    rw [heq]
    exact lorentz_integrable
  · rw [scaled_exp_integral u hu, heq]
    exact lorentz_integral

private lemma master_pullback (x s : ℝ) :
    Real.exp s * (1 / ((x + Real.exp s) *
      ((Real.log (Real.exp s)) ^ 2 + Real.pi ^ 2))) = stripWeight x s := by
  simp [Real.log_exp, stripWeight, div_eq_mul_inv]

private lemma master_exp_substitution (x : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
      1 / ((x + t) * ((Real.log t) ^ 2 + Real.pi ^ 2))) =
      ∫ s : ℝ, stripWeight x s := by
  rw [scaled_exp_integral 1 zero_lt_one]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [one_mul] using master_pullback x s)

private theorem master_integrable (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ =>
      1 / ((x + t) * ((Real.log t) ^ 2 + Real.pi ^ 2))) (Set.Ioi 0) := by
  apply (scaled_exp_integrable_iff 1 zero_lt_one _).mpr
  simpa only [one_mul, master_pullback] using stripWeight_integrable x hx

private lemma stripWeight_one_reflection (s : ℝ) :
    stripWeight 1 s + stripWeight 1 (-s) = 1 / (s ^ 2 + Real.pi ^ 2) := by
  unfold stripWeight
  rw [Real.exp_neg]
  have hd : s ^ 2 + Real.pi ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have he : Real.exp s ≠ 0 := Real.exp_ne_zero s
  have hp : 1 + Real.exp s ≠ 0 := ne_of_gt (by positivity)
  have hn : 1 + (Real.exp s)⁻¹ ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

private theorem master_integral_one :
    IntegrableOn (fun t : ℝ =>
      1 / ((1 + t) * ((Real.log t) ^ 2 + Real.pi ^ 2))) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ),
      1 / ((1 + t) * ((Real.log t) ^ 2 + Real.pi ^ 2))) = 1 / 2 := by
  refine ⟨master_integrable 1 zero_lt_one, ?_⟩
  rw [master_exp_substitution]
  have hi := stripWeight_integrable 1 zero_lt_one
  have hneg : (∫ s : ℝ, stripWeight 1 (-s)) = ∫ s : ℝ, stripWeight 1 s := by
    simpa using MeasureTheory.Measure.integral_comp_mul_left (stripWeight 1) (-1)
  have hmass := (logarithmic_density_mass 1 zero_lt_one).2
  rw [scaled_exp_integral 1 zero_lt_one] at hmass
  have heq : (fun s : ℝ => (1 * Real.exp s) *
      (1 / ((1 * Real.exp s) * ((Real.log (1 * Real.exp s / 1)) ^ 2 + Real.pi ^ 2)))) =
      (fun s : ℝ => 1 / (s ^ 2 + Real.pi ^ 2)) := by
    funext s
    simp only [one_mul, div_one, Real.log_exp]
    field_simp [Real.exp_ne_zero]
  rw [heq] at hmass
  have hsum := integral_congr_ae (μ := volume)
    (Filter.Eventually.of_forall stripWeight_one_reflection)
  rw [integral_add hi hi.comp_neg, hneg, hmass] at hsum
  linarith

theorem master_integral (x : ℝ) (hx : 0 < x) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      1 / ((x + t) * ((Real.log t) ^ 2 + Real.pi ^ 2))) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ),
      1 / ((x + t) * ((Real.log t) ^ 2 + Real.pi ^ 2))) = masterValue x := by
  refine ⟨master_integrable x hx, ?_⟩
  by_cases h : x = 1
  · subst x
    simpa [masterValue] using master_integral_one.2
  · rw [master_exp_substitution, stripWeight_integral x hx h, masterValue, if_neg h]

end D5.S3.Quantum.PositiveResolvent.LogarithmicIntegral
