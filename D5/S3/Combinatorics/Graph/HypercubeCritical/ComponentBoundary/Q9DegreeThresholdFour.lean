/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeThresholdFour
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeThresholdFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Optimal induced maximum degree at 260 vertices of Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BalancedComponentExcess
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Gray54ExtensionBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DegreeFourWitness
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixClosingCertificates

/-! At order 260, the Gray54 extension obstruction forces every Huang-balanced
cubic component of a subcubic candidate to have at least 72 vertices. Rank-nullity
requires at least four such components. Both ninth-coordinate lifts of the
130-point construction of Hong–Wu–Xia (arXiv:2610.09483v1, Proposition 6.2)
attain maximum degree four. This gives their parameter value `f₄(Q₉) = 4`.
Their question about `f₂(Q₉)` at 258 vertices remains open. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DegreeThresholdFour

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)

open Classical in
/-- Every induced subcubic vertex set in the nine-cube has at most 259 points. -/
private theorem subcubic_card_le_259 (U : Finset (Q 9))
    (hdeg : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3) :
    U.card ≤ 259 := by
  by_contra! h260
  have hdeg' (v : (U : Set (Q 9))) :
      ((hypercube 9).induce (U : Set (Q 9))).degree v ≤ 3 :=
    (SimpleGraph.degree_le_maxDegree _ _).trans hdeg
  apply not_le_of_gt h260
  apply Q9BalancedComponentExcess.card_le_259_of_seventy_two_le U hdeg'
  intro C hCU hCn hclosed hr hb
  rcases q9_balanced_induced_cubic_small_orders C hCn hr hb with
    h54 | h72
  · have h257 := Q9Gray54ExtensionBound.card_le_of_balanced_cubic_fifty_four
      U C h54 hr hb hCU hclosed hdeg'
    omega
  · exact h72

open Classical in
/-- Every 260-vertex set has induced maximum degree at least four. -/
theorem four_le_maxDegree_of_card_260 (U : Finset (Q 9)) (hU : U.card = 260) :
    4 ≤ ((hypercube 9).induce (U : Set (Q 9))).maxDegree := by
  by_contra! h4
  have h := subcubic_card_le_259 U (by omega)
  omega

open Classical in
/-- A 260-vertex induced subgraph of the nine-cube attains maximum degree four. -/
theorem exists_card_260_maxDegree_eq_four :
    ∃ U : Finset (Q 9), U.card = 260 ∧
      ((hypercube 9).induce (U : Set (Q 9))).maxDegree = 4 := by
  obtain ⟨U, hU, hle⟩ := Q9DegreeFourWitness.exists_card_260_maxDegree_le_four
  exact ⟨U, hU, le_antisymm hle (four_le_maxDegree_of_card_260 U hU)⟩

#print axioms subcubic_card_le_259
#print axioms four_le_maxDegree_of_card_260
#print axioms exists_card_260_maxDegree_eq_four

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DegreeThresholdFour
