/- GID: D5/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative remaining energy bounds total radiation and constant-power duration. -/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Dynamics.FiniteEnergyRadiationBudget

open Set Filter MeasureTheory
open scoped Topology

private theorem remaining_energy_limit {E P : ℝ → ℝ} {u₀ : ℝ}
    (hderiv : ∀ u ∈ Ioi u₀, HasDerivAt E (-(P u)) u)
    (hcont : ContinuousWithinAt E (Ici u₀) u₀)
    (hE : ∀ u ∈ Ici u₀, 0 ≤ E u) (hP : ∀ u ∈ Ici u₀, 0 ≤ P u) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto E atTop (𝓝 L) := by
  have hc : ContinuousOn E (Ici u₀) := by
    intro u hu
    rcases (mem_Ici.mp hu).eq_or_lt with rfl | hu
    · exact hcont
    · exact (hderiv u (mem_Ioi.mpr hu)).continuousAt.continuousWithinAt
  have ha : AntitoneOn E (Ici u₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici u₀) hc
    · intro u hu
      rw [interior_Ici] at hu
      exact (hderiv u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      rw [(hderiv u hu).deriv]
      exact neg_nonpos.mpr (hP u (mem_Ici.mpr (mem_Ioi.mp hu).le))
  let F : ℝ → ℝ := fun u => E (max u₀ u)
  have hF : Antitone F := fun u v huv =>
    ha (mem_Ici.mpr (le_max_left _ _)) (mem_Ici.mpr (le_max_left _ _))
      (max_le_max_left _ huv)
  have hF₀ : ∀ u, 0 ≤ F u := fun u => hE _ (mem_Ici.mpr (le_max_left _ _))
  have hb : BddBelow (range F) := ⟨0, by
    rintro _ ⟨u, rfl⟩
    exact hF₀ u⟩
  refine ⟨⨅ u, F u, le_ciInf hF₀, ?_⟩
  apply (tendsto_atTop_ciInf hF hb).congr'
  filter_upwards [eventually_ge_atTop u₀] with u hu
  simp only [F, max_eq_right hu]

/-- The radiated power is integrable and its total does not exceed the initial energy.
The energy balance holds after the initial time, with right continuity at that time. -/
theorem finite_energy_radiation_budget {E P : ℝ → ℝ} {u₀ : ℝ}
    (hderiv : ∀ u ∈ Ioi u₀, HasDerivAt E (-(P u)) u)
    (hcont : ContinuousWithinAt E (Ici u₀) u₀)
    (hE : ∀ u ∈ Ici u₀, 0 ≤ E u) (hP : ∀ u ∈ Ici u₀, 0 ≤ P u) :
    IntegrableOn P (Ioi u₀) ∧ (∫ u in Ioi u₀, P u) ≤ E u₀ := by
  obtain ⟨L, hL, hlim⟩ := remaining_energy_limit hderiv hcont hE hP
  have hi : IntegrableOn (fun u => -(P u)) (Ioi u₀) :=
    integrableOn_Ioi_deriv_of_nonpos hcont hderiv
      (fun u hu => neg_nonpos.mpr (hP u (mem_Ici.mpr (mem_Ioi.mp hu).le))) hlim
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hi hlim
  rw [integral_neg] at heq
  refine ⟨?_, ?_⟩
  · exact integrable_neg_iff.mp hi
  · linarith

/-- A constant positive power on the initial interval has duration at most E(u₀) / P₀. -/
theorem constant_power_duration_le {E P : ℝ → ℝ} {u₀ Δ P₀ : ℝ}
    (hderiv : ∀ u ∈ Ioi u₀, HasDerivAt E (-(P u)) u)
    (hcont : ContinuousWithinAt E (Ici u₀) u₀)
    (hE : ∀ u ∈ Ici u₀, 0 ≤ E u) (hP : ∀ u ∈ Ici u₀, 0 ≤ P u)
    (hΔ : 0 ≤ Δ) (hP₀ : 0 < P₀) (hconstant : ∀ u ∈ Icc u₀ (u₀ + Δ), P u = P₀) :
    Δ ≤ E u₀ / P₀ := by
  obtain ⟨hi, hbudget⟩ := finite_energy_radiation_budget hderiv hcont hE hP
  have hle : u₀ ≤ u₀ + Δ := le_add_of_nonneg_right hΔ
  have hsegment : (∫ u in Ioc u₀ (u₀ + Δ), P u) = Δ * P₀ := by
    rw [← intervalIntegral.integral_of_le hle]
    calc
      (∫ u in u₀..u₀ + Δ, P u) = ∫ _ in u₀..u₀ + Δ, P₀ := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hconstant u (by simpa only [uIcc_of_le hle] using hu)
      _ = Δ * P₀ := by simp only [intervalIntegral.integral_const, add_sub_cancel_left,
          smul_eq_mul]
  have hmono : (∫ u in Ioc u₀ (u₀ + Δ), P u) ≤ ∫ u in Ioi u₀, P u := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hP u (mem_Ici.mpr (mem_Ioi.mp hu).le)
    · exact ae_of_all _ (fun u hu => mem_Ioi.mpr (mem_Ioc.mp hu).1)
  apply (le_div_iff₀ hP₀).mpr
  rw [hsegment] at hmono
  exact hmono.trans hbudget

#print axioms finite_energy_radiation_budget
#print axioms constant_power_duration_le

end D5.S3.Quantum.Dynamics.FiniteEnergyRadiationBudget
