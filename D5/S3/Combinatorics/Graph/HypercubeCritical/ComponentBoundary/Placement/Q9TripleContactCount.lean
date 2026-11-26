/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TripleContactCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TripleContactCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: At distance three, a nonempty parity family of contacts has at least fifteen displacements. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.TripleContactFamilyBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

/-! The fifteen-displacement bound at minimum distance three in the nine-cube. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TripleContactCount

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements)
open TripleContactFamilyBound (eq_five_axis_powerset_or_card_ge_fifteen_of_three_extensions)
open Q9TightContactStar (minimum_displacements_card_strict)
open private mem_minimumDisplacements minimum_displacements_three_extensions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

open Classical in
/-- Under the weighted support hypotheses, a balanced cubic support has at
least fifteen minimum displacements at distance three on each occupied parity. -/
theorem fifteen_minimum_displacements_at_distance_three
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 3 ≤ hammingDist u v)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hne : (minimumDisplacements C D b 3).Nonempty)
    (hC : ∀ i, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0))
    (hD : ∀ c, ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = c) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)) :
    15 ≤ (minimumDisplacements C D b 3).card := by
  have hsize (T : Finset (Fin 9)) (hT : T ∈ minimumDisplacements C D b 3) : T.card = 3 := by
    obtain ⟨x, _, y, _, _, hdist, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hdist
  rcases eq_five_axis_powerset_or_card_ge_fifteen_of_three_extensions _ hne hsize
      (minimum_displacements_three_extensions C D b 3 hsep hC hD) with ⟨A, hA, hAeq⟩ | h15
  · have hstrict := minimum_displacements_card_strict (by decide) hsep hr hb hne hC hD
    rw [hAeq, Finset.card_powersetCard, hA] at hstrict
    exact False.elim ((by decide : ¬ (3 + 2).choose 2 < (5 : ℕ).choose 3) hstrict)
  · exact h15

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TripleContactCount
