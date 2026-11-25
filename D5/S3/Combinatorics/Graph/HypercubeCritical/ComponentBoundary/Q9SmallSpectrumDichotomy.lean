/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Eight-star packing and parity arithmetic reduce the smallest remaining component orders. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureParityLayers
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarFootprintPacking
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DescendingEdgeParity

/-!
# Parity constraints on the smallest remaining orders

For Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2. The hypothesis on every
axis is the geometric alternative left by excluding positive blocks of
orders nine, ten, and eleven: a full eight-star or at least twelve paired
fibres of one projected parity. The star packing theorem forbids all nine
axes from being stars in a set of at most 258 vertices. The parity identity
then leaves a pure-parity component at order 72, rules out order 78, and
rules out order 84 by the descending-edge parity invariant in the nine axes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallSpectrumDichotomy

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open Q9OccupiedFibreParity (doubleFibres)
open Q9TwoStarAxisBound (EightStar)
open Q9EightStarFootprintPacking (not_all_axes_eight_stars doubleFibres_ge_two_of_eightStar)
open Q9PureParityLayers (projected_vertex_identity)
open private doubleFibres_partition projectedVertices from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

attribute [local instance] Classical.propDecidable

/-- The geometric alternative left by the local small-support exclusion. -/
def SmallBlockAlternative (C : Finset (Q 9)) (i : Fin 9) : Prop :=
  (∃ (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B) ∨
  ∃ p : Bool, 12 ≤ (doubleFibres C i p).card

private theorem axis_counts {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (i : Fin 9) (m : ℕ) (hC : C.card = 6 * m) :
    directionEdges C i = m := by
  have h := direction_edge_count (d := 3) C hr hb i
  omega

private theorem pure_of_twelve {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {i : Fin 9} (hm : directionEdges C i = 12)
    {p : Bool} (hp : 12 ≤ (doubleFibres C i p).card) :
    (doubleFibres C i p).card = 12 ∧ (doubleFibres C i (!p)).card = 0 := by
  have hpart := doubleFibres_partition C i p
  omega

/-- Under the local alternative, a 72-vertex cubic component must be pure
on every axis: a single full star would force a minority pair count on all
other axes, so no other axis could realize the twelve-pair alternative. -/
theorem pure_parity_of_order_seventy_two {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hC : C.card = 72) (halt : ∀ i, SmallBlockAlternative C i) :
    ∀ i : Fin 9, ∃ p : Bool, (doubleFibres C i (!p)).card = 0 := by
  have hm (i : Fin 9) : directionEdges C i = 12 := axis_counts hr hb i 12 hC
  have hn : ¬ ∃ (i : Fin 9) (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B := by
    rintro ⟨i, c, A, B, hstar⟩
    apply not_all_axes_eight_stars hr (by omega : C.card ≤ 258)
    intro j
    by_cases h : j = i
    · subst j
      exact ⟨c, A, B, hstar⟩
    · rcases halt j with hj | ⟨p, hp⟩
      · exact hj
      · have hminor := doubleFibres_ge_two_of_eightStar hr hstar h (!p)
        have hpart := doubleFibres_partition C j p
        have he := hm j
        omega
  intro i
  rcases halt i with ⟨c, A, B, hstar⟩ | ⟨p, hp⟩
  · exact (hn ⟨i, c, A, B, hstar⟩).elim
  · exact ⟨p, (pure_of_twelve hr hb (hm i) hp).2⟩

/-- At order 78 no projected parity has twelve paired fibres, by divisibility
of the projected vertex count. All nine axes would therefore be full stars. -/
theorem order_ne_seventy_eight {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (halt : ∀ i, SmallBlockAlternative C i) : C.card ≠ 78 := by
  intro hC
  have hm (i : Fin 9) : directionEdges C i = 13 := axis_counts hr hb i 13 hC
  apply not_all_axes_eight_stars hr (by omega : C.card ≤ 258)
  intro i
  rcases halt i with hi | ⟨p, hp⟩
  · exact hi
  · have hpart := doubleFibres_partition C i p
    have hid := projected_vertex_identity hr hb i p
    have he := hm i
    omega

/-- If one projected parity contains twelve pairs out of fourteen, it contains
exactly thirteen. No full eight-star can occur on another axis. Thus every
axis of an order-84 component has precisely one minority pair. -/
theorem thirteen_and_one_of_order_eighty_four {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hC : C.card = 84) (halt : ∀ i, SmallBlockAlternative C i) :
    ∀ i : Fin 9, ∃ p : Bool, (doubleFibres C i p).card = 13 ∧
      (doubleFibres C i (!p)).card = 1 := by
  have hm (i : Fin 9) : directionEdges C i = 14 := axis_counts hr hb i 14 hC
  have hlarge (i : Fin 9) (p : Bool) (hp : 12 ≤ (doubleFibres C i p).card) :
      (doubleFibres C i p).card = 13 ∧ (doubleFibres C i (!p)).card = 1 := by
    have hpart := doubleFibres_partition C i p
    have hid := projected_vertex_identity hr hb i p
    have he := hm i
    omega
  have hn : ¬ ∃ (i : Fin 9) (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B := by
    rintro ⟨i, c, A, B, hstar⟩
    apply not_all_axes_eight_stars hr (by omega : C.card ≤ 258)
    intro j
    by_cases h : j = i
    · subst j
      exact ⟨c, A, B, hstar⟩
    · rcases halt j with hj | ⟨p, hp⟩
      · exact hj
      · have hminor := doubleFibres_ge_two_of_eightStar hr hstar h (!p)
        have hlarge' := (hlarge j p hp).2
        omega
  intro i
  rcases halt i with ⟨c, A, B, hstar⟩ | ⟨p, hp⟩
  · exact (hn ⟨i, c, A, B, hstar⟩).elim
  · exact ⟨p, hlarge i p hp⟩

/-- The all-axis 13/1 split has odd total in the odd projected parity.
Huang balance requires that total to be even. -/
theorem order_ne_eighty_four {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (halt : ∀ i, SmallBlockAlternative C i) : C.card ≠ 84 := by
  intro hC
  apply Q9DescendingEdgeParity.not_all_axes_split_thirteen_one hr hb
  intro i
  obtain ⟨p, hp, hminor⟩ := thirteen_and_one_of_order_eighty_four hr hb hC halt i
  cases p
  · exact Or.inl ⟨hp, hminor⟩
  · exact Or.inr ⟨hminor, hp⟩

/-- Once the pure adjacent-layer case of order 72 is excluded, the first
remaining order under the local block alternative is 90. -/
theorem ninety_le_of_not_seventy_two {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (halt : ∀ i, SmallBlockAlternative C i)
    (h72 : C.card ≠ 72) : 90 ≤ C.card := by
  let m := directionEdges C (0 : Fin 9)
  have hC : C.card = 6 * m := (direction_edge_count (d := 3) C hr hb 0).symm
  have hm : 12 ≤ m := by
    by_contra h
    apply not_all_axes_eight_stars hr (by omega : C.card ≤ 258)
    intro i
    rcases halt i with hs | ⟨p, hp⟩
    · exact hs
    · have he := axis_counts hr hb i m hC
      have hpart := doubleFibres_partition C i p
      omega
  have h78 := order_ne_seventy_eight hr hb halt
  have h84 := order_ne_eighty_four hr hb halt
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallSpectrumDichotomy
