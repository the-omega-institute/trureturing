/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ThreeFlipProjectedParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ThreeFlipProjectedParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod]
   utility: none
   digest: Even neighbor counts for occupied fibers, their complement and antipodal labels. -/

import D5.S3.Combinatorics.Graph.Hypercube
import Mathlib.Algebra.CharP.Two
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.ZMod.Basic

/-! Sum the product-cube adjacency equation over a set of three-coordinate vertices
whose incidence parity is the indicator of its complement. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThreeFlipProjectedParity

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube hypercube_regular)

local notation "Q₃" => (Fin 3 → Bool)
local notation "Q₆" => (Fin 6 → Bool)

/-- The selected three-coordinate vertices over a fixed six-coordinate vertex. -/
def fiber (S : Finset (Q₃ × Q₆)) (y : Q₆) : Finset Q₃ :=
  Finset.univ.filter fun p => (p, y) ∈ S

/-- Each fiber is empty or consists of the endpoints of a cube edge. -/
def EdgeFibers (S : Finset (Q₃ × Q₆)) : Prop :=
  ∀ y, fiber S y = ∅ ∨ ∃ a b, (hypercube 3).Adj a b ∧ fiber S y = {a, b}

/-- The projection onto the six-coordinate cube. -/
def occupied (S : Finset (Q₃ × Q₆)) : Finset Q₆ :=
  Finset.univ.filter fun y => (fiber S y).Nonempty

private def evenVertices : Finset Q₃ :=
  Finset.univ.filter fun p => (Finset.univ.filter fun i => p i = true).card % 2 = 0

private def antipodalPair (a : Q₃) : Finset Q₃ := {a, fun i => !a i}

/-- Fibers meeting the antipodal label represented by `a`. -/
def labelSupport (S : Finset (Q₃ × Q₆)) (a : Q₃) : Finset Q₆ :=
  Finset.univ.filter fun y => (antipodalPair a ∩ fiber S y).Nonempty

private def indicator {α : Type*} [DecidableEq α] (S : Finset α) (v : α) : ZMod 2 :=
  if v ∈ S then 1 else 0

open Classical in
/-- The unsigned adjacency equation on the product cube, reduced modulo two. -/
def UnsignedAdjacencyParity (S : Finset (Q₃ × Q₆)) : Prop :=
  ∀ v : Q₃ × Q₆,
    ((((hypercube 3).boxProd (hypercube 6)).neighborFinset v ∩ S).card : ZMod 2) =
      if v ∈ S then 1 else 0

section

local instance : DecidableRel (hypercube 3).Adj :=
  fun a b => inferInstanceAs (Decidable (hammingDist a b = 1))

private def adjacencyBit (p q : Q₃) : ZMod 2 :=
  if (hypercube 3).Adj p q then 1 else 0

-- The even-vertex set contributes three incidences at each odd vertex and zero at each even one.
private theorem even_incidence (q : Q₃) :
    (∑ p ∈ evenVertices, adjacencyBit p q) + indicator evenVertices q = 1 :=
  (by decide : ∀ q : Q₃,
    (∑ p ∈ evenVertices, adjacencyBit p q) + indicator evenVertices q = 1) q

-- Every vertex outside an antipodal pair has exactly one neighbor in that pair.
private theorem antipodal_incidence (a q : Q₃) :
    (∑ p ∈ antipodalPair a, adjacencyBit p q) + indicator (antipodalPair a) q = 1 :=
  (by decide : ∀ a q : Q₃,
    (∑ p ∈ antipodalPair a, adjacencyBit p q) + indicator (antipodalPair a) q = 1) a q

private theorem even_edge (a b : Q₃) (hab : (hypercube 3).Adj a b) :
    (evenVertices ∩ {a, b}).card = 1 :=
  (by decide : ∀ a b : Q₃, (hypercube 3).Adj a b → (evenVertices ∩ {a, b}).card = 1)
    a b hab

private theorem antipodal_edge (a b c : Q₃) (hbc : (hypercube 3).Adj b c) :
    (antipodalPair a ∩ {b, c}).card ≤ 1 :=
  (by decide : ∀ a b c : Q₃, (hypercube 3).Adj b c →
    (antipodalPair a ∩ {b, c}).card ≤ 1) a b c hbc

end

private theorem sum_neighbor_indicator {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (S : Finset α) (v : α) [Fintype (G.neighborSet v)] :
    (∑ w ∈ G.neighborFinset v, indicator S w) = ((G.neighborFinset v ∩ S).card : ZMod 2) := by
  simp only [indicator, Finset.sum_boole, Finset.filter_mem_eq_inter]

private theorem sum_fiber_indicator (S : Finset (Q₃ × Q₆)) (T : Finset Q₃) (y : Q₆) :
    (∑ p ∈ T, indicator S (p, y)) = ((T ∩ fiber S y).card : ZMod 2) := by
  simp only [indicator, Finset.sum_boole]
  exact congrArg (fun s : Finset Q₃ => (s.card : ZMod 2)) (by ext p; simp [fiber])

open Classical in
private theorem row_sum (S : Finset (Q₃ × Q₆)) (hS : UnsignedAdjacencyParity S)
    (p : Q₃) (y : Q₆) :
    (∑ q ∈ (hypercube 3).neighborFinset p, indicator S (q, y)) +
      (∑ z ∈ (hypercube 6).neighborFinset y, indicator S (p, z)) = indicator S (p, y) := by
  have h := hS (p, y)
  change _ = indicator S (p, y) at h
  rw [← sum_neighbor_indicator ((hypercube 3).boxProd (hypercube 6)) S (p, y),
    SimpleGraph.neighborFinset_boxProd, Finset.sum_disjUnion,
    Finset.sum_product, Finset.sum_product] at h
  simpa only [Prod.fst, Prod.snd, Finset.sum_singleton] using h

open Classical in
private theorem projected_even (S : Finset (Q₃ × Q₆)) (hS : UnsignedAdjacencyParity S)
    (hEdge : EdgeFibers S) (T : Finset Q₃) (P : Finset Q₆)
    (hIncidence : ∀ q : Q₃, (∑ p ∈ T, adjacencyBit p q) + indicator T q = 1)
    (hProjection : ∀ y : Q₆, ((T ∩ fiber S y).card : ZMod 2) = indicator P y) :
    ∀ y, Even ((hypercube 6).neighborFinset y ∩ P).card := by
  intro y
  let c : Q₃ → ZMod 2 := fun q => indicator S (q, y)
  have htotal : ∑ q, c q = 0 := by
    have h := sum_fiber_indicator S Finset.univ y
    simp only [Finset.univ_inter] at h
    change ∑ q, c q = _
    rw [h]
    rcases hEdge y with hf | ⟨a, b, hab, hf⟩
    · simp [hf]
    · simp [hf, (hypercube 3).ne_of_adj hab, CharTwo.two_eq_zero]
  have hhorizontal :
      (∑ p ∈ T, ∑ q ∈ (hypercube 3).neighborFinset p, c q) = ∑ q ∈ T, c q := by
    have hcount :
        (∑ p ∈ T, ∑ q ∈ (hypercube 3).neighborFinset p, c q) =
          ∑ q, (∑ p ∈ T, adjacencyBit p q) * c q := by
      simp_rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro p _
      by_cases hpq : (hypercube 3).Adj p q <;> simp [adjacencyBit, hpq]
    have hsel : (∑ q, indicator T q * c q) = ∑ q ∈ T, c q := by
      simp [indicator, ite_mul]
    apply eq_of_sub_eq_zero
    rw [CharTwo.sub_eq_add, hcount, ← hsel, ← Finset.sum_add_distrib]
    simpa only [← add_mul, hIncidence, one_mul] using htotal
  have hsum := Finset.sum_congr (rfl : T = T) (fun p _ => row_sum S hS p y)
  rw [Finset.sum_add_distrib] at hsum
  change (∑ p ∈ T, ∑ q ∈ (hypercube 3).neighborFinset p, c q) +
    (∑ p ∈ T, ∑ z ∈ (hypercube 6).neighborFinset y, indicator S (p, z)) =
    ∑ p ∈ T, c p at hsum
  rw [hhorizontal, add_eq_left, Finset.sum_comm] at hsum
  simp_rw [sum_fiber_indicator, hProjection] at hsum
  rw [sum_neighbor_indicator (hypercube 6) P y] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

open Classical in
/-- Both the occupied projection and its complement have even neighbor counts
at every vertex of the six-cube. -/
theorem occupied_and_complement_even (S : Finset (Q₃ × Q₆)) (hS : UnsignedAdjacencyParity S)
    (hEdge : EdgeFibers S) (y : Q₆) :
    Even ((hypercube 6).neighborFinset y ∩ occupied S).card ∧
      Even ((hypercube 6).neighborFinset y ∩ (Finset.univ \ occupied S)).card := by
  have hProjection (z : Q₆) :
      ((evenVertices ∩ fiber S z).card : ZMod 2) = indicator (occupied S) z := by
    rcases hEdge z with hf | ⟨a, b, hab, hf⟩
    · simp [indicator, occupied, hf]
    · simp [indicator, occupied, hf, even_edge a b hab]
  have hF := projected_even S hS hEdge evenVertices (occupied S) even_incidence hProjection y
  refine ⟨hF, ?_⟩
  let N := (hypercube 6).neighborFinset y
  have hN : N.card = 6 := (hypercube_regular 6).degree_eq y
  have hsplit := Finset.card_inter_add_card_sdiff N (occupied S)
  have hdiff : N ∩ (Finset.univ \ occupied S) = N \ occupied S := by
    rw [← Finset.inter_sdiff_assoc, Finset.inter_univ]
  change Even (N ∩ (Finset.univ \ occupied S)).card
  rw [hdiff]
  obtain ⟨k, hk⟩ := hF
  change (N ∩ occupied S).card = k + k at hk
  exact ⟨3 - k, by omega⟩

open Classical in
/-- Each antipodal label support has even neighbor counts at every vertex of the six-cube. -/
theorem antipodal_label_even (S : Finset (Q₃ × Q₆)) (hS : UnsignedAdjacencyParity S)
    (hEdge : EdgeFibers S) (a : Q₃) (y : Q₆) :
    Even ((hypercube 6).neighborFinset y ∩ labelSupport S a).card := by
  refine projected_even S hS hEdge (antipodalPair a) (labelSupport S a)
    (antipodal_incidence a) ?_ y
  intro z
  simp only [indicator, labelSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    ← Finset.card_pos]
  rcases hEdge z with hf | ⟨b, c, hbc, hf⟩
  · simp [hf]
  · rw [hf]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (antipodal_edge a b c hbc) with h | h <;> simp [h]

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThreeFlipProjectedParity
