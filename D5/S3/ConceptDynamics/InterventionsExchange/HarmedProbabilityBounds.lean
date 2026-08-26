/- GID: D5/S3/ConceptDynamics/InterventionsExchange/HarmedProbabilityBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/HarmedProbabilityBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Frechet lower and upper bounds for harmed potential-outcome probability. -/

import Mathlib.Data.Bool.Basic
import Mathlib.MeasureTheory.Measure.Real

/- Library-search audit trail (2026-08-26):
   * `rg -n -i 'frechet|frechet.*bound|harmed probability' D5` found no exact
     repository theorem.
   * Pinned Mathlib supplies `measureReal_mono`, `measureReal_union_le`,
     `measureReal_compl`, and `probReal_univ`; these are the direct measure
     primitives used below.
   * Body-shape checks for `Measure.real {x | x.1 = true}`, the cross-world
     harmed event, and this max/min conjunction found no existing D5 declaration.
   * No Galois or product-singularity theorem was reused: those searches were
     misses for the other lease atoms.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.HarmedProbabilityBounds

open MeasureTheory Set

/-- For a joint law of the two Boolean potential outcomes, the probability of
being harmed lies between the sharp Frechet bounds from its marginals. -/
theorem harmed_probability_frechet_bound (μ : Measure (Bool × Bool))
    [IsProbabilityMeasure μ] :
    let p₀ := μ.real {ω | ω.1 = true}
    let p₁ := μ.real {ω | ω.2 = true}
    let h := μ.real {ω | ω.1 = true ∧ ω.2 = false}
    max 0 (p₀ - p₁) ≤ h ∧ h ≤ min p₀ (1 - p₁) := by
  let a : Set (Bool × Bool) := {ω | ω.1 = true}
  let b : Set (Bool × Bool) := {ω | ω.2 = true}
  let c : Set (Bool × Bool) := {ω | ω.1 = true ∧ ω.2 = false}
  change max 0 (μ.real a - μ.real b) ≤ μ.real c ∧
    μ.real c ≤ min (μ.real a) (1 - μ.real b)
  have ha : MeasurableSet a := MeasurableSet.of_discrete
  have hb : MeasurableSet b := MeasurableSet.of_discrete
  have hc : MeasurableSet c := MeasurableSet.of_discrete
  have hca : c ⊆ a := by
    intro ω hω
    change ω.1 = true ∧ ω.2 = false at hω
    change ω.1 = true
    exact hω.1
  have hcb : c ⊆ bᶜ := by
    intro ω hω hωb
    change ω.1 = true ∧ ω.2 = false at hω
    change ω.2 = true at hωb
    exact Bool.noConfusion (hωb.symm.trans hω.2)
  have hacb : a ⊆ c ∪ b := by
    intro ω hω
    change ω.1 = true at hω
    cases hω₂ : ω.2 with
    | false =>
        exact Or.inl (show ω ∈ c by
          change ω.1 = true ∧ ω.2 = false
          exact ⟨hω, hω₂⟩)
    | true =>
        exact Or.inr (show ω ∈ b by
          change ω.2 = true
          exact hω₂)
  have hc_le_a : μ.real c ≤ μ.real a := measureReal_mono hca
  have hc_le_compl_b : μ.real c ≤ μ.real bᶜ := measureReal_mono hcb
  have hc_le_one_sub_b : μ.real c ≤ 1 - μ.real b := by
    simpa [measureReal_compl hb] using hc_le_compl_b
  have ha_le_hc_add_b : μ.real a ≤ μ.real c + μ.real b := by
    exact (measureReal_mono hacb).trans (measureReal_union_le c b)
  have h_lower : μ.real a - μ.real b ≤ μ.real c := by
    linarith
  have h_nonneg : 0 ≤ μ.real c := measureReal_nonneg
  refine ⟨?_, ?_⟩
  · exact max_le h_nonneg h_lower
  · exact le_min hc_le_a hc_le_one_sub_b

#print axioms harmed_probability_frechet_bound

end D5.S3.ConceptDynamics.InterventionsExchange.HarmedProbabilityBounds
