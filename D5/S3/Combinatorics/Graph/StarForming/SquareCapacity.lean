/- GID: D5/S3/Combinatorics/Graph/StarForming/SquareCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SquareCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Uniform nonnegative square weights bound the actual finite dissociation maximum. -/

import D5.S3.Combinatorics.Graph.StarForming.BipartiteBounds
import D5.S3.Combinatorics.Graph.StarForming.DissociationCover
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-! This is the graph-wide finite weighted summation from the received cover
note. Squares need not be induced, and no strict cover gain or star-forming
identification follows from this certificate. -/

namespace D5.S3.Combinatorics.Graph.StarForming.SquareCapacity
open StarFormingDissociationRefutation
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Four distinct vertices with the four cyclic edges; diagonals are allowed. -/
structure Square (G : SimpleGraph V) where
  vertex : Fin 4 → V
  injective : Function.Injective vertex
  edge01 : G.Adj (vertex 0) (vertex 1)
  edge12 : G.Adj (vertex 1) (vertex 2)
  edge23 : G.Adj (vertex 2) (vertex 3)
  edge30 : G.Adj (vertex 3) (vertex 0)

def Square.carrier {G : SimpleGraph V} (C : Square G) : Finset V :=
  Finset.univ.image C.vertex

/-- Each actual square has four vertices, not four possibly repeated labels. -/
theorem carrier_card {G : SimpleGraph V} (C : Square G) : C.carrier.card = 4 := by
  rw [Square.carrier,Finset.card_image_of_injective _ C.injective]
  simp

/-- No dissociation selection uses three vertices of a square. -/
theorem intersection_cap (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : IsKIndependent G 2 S) (C : Square G) :
    (S ∩ C.carrier).card ≤ 2 := by
  classical
  have hd : DissociationCover.Dissociates G.Adj (· ∈ S) := by
    intro center first second hc hf hs ha hb
    exact (SubQuorum.DoubleStarGrafting.independent_iff G S).mp hS
      center hc first hf second hs ha hb
  have hne02 : C.vertex 0 ≠ C.vertex 2 := fun h => (by decide : (0 : Fin 4) ≠ 2)
    (C.injective h)
  have hne13 : C.vertex 1 ≠ C.vertex 3 := fun h => (by decide : (1 : Fin 4) ≠ 3)
    (C.injective h)
  have ht := DissociationCover.four_cycle_excludes_triples (fun _ _ h => G.adj_symm h)
    hd (C.vertex 0) (C.vertex 1) (C.vertex 2) (C.vertex 3) hne02 hne13
    C.edge01 C.edge12 C.edge23 C.edge30
  let A : Finset (Fin 4) := Finset.univ.filter (fun i => C.vertex i ∈ S)
  have he : S ∩ C.carrier = A.image C.vertex := by
    ext v
    simp only [Finset.mem_inter,Square.carrier,Finset.mem_image,Finset.mem_univ,
      true_and,A,Finset.mem_filter]
    constructor
    · rintro ⟨hs,i,rfl⟩
      exact ⟨i,hs,rfl⟩
    · rintro ⟨i,hs,rfl⟩
      exact ⟨hs,i,rfl⟩
  have hsmall : ∀ B : Finset (Fin 4),
      (¬ (0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B)) ∧ (¬ (1 ∈ B ∧ 2 ∈ B ∧ 3 ∈ B)) ∧
      (¬ (2 ∈ B ∧ 3 ∈ B ∧ 0 ∈ B)) ∧ (¬ (3 ∈ B ∧ 0 ∈ B ∧ 1 ∈ B)) →
        B.card ≤ 2 := by decide +kernel
  rw [he,Finset.card_image_of_injective _ C.injective]
  apply hsmall A
  simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using ht

/-- Finite weighted incidence double counting, with the selected set arbitrary. -/
theorem weighted_intersections {Q : Type*} [Fintype Q]
    (C : Q → Finset V) (weight : Q → ℚ) (S : Finset V) :
    ∑ q : Q, weight q * ((S ∩ C q).card : ℚ) =
      ∑ v ∈ S, ∑ q : Q, if v ∈ C q then weight q else 0 := by
  classical
  have hc (q : Q) : ((S ∩ C q).card : ℚ) =
      ∑ v ∈ S, if v ∈ C q then (1 : ℚ) else 0 := by
    rw [← Finset.sum_filter]
    have he : S.filter (fun v => v ∈ C q) = S ∩ C q := by ext v; simp
    rw [he]
    simp
  simp_rw [hc,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]

/-- Uniform vertex capacity exactly counts every selected vertex once. -/
theorem uniform_intersections {Q : Type*} [Fintype Q]
    (C : Q → Finset V) (weight : Q → ℚ)
    (huniform : ∀ v, (∑ q : Q, if v ∈ C q then weight q else 0) = 1)
    (S : Finset V) :
    ∑ q : Q, weight q * ((S ∩ C q).card : ℚ) = S.card := by
  rw [weighted_intersections]
  simp_rw [huniform]
  simp

/-- An actual nonnegative uniform square certificate bounds every selection. -/
theorem selection_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ)
    (hweight : ∀ q, 0 ≤ weight q)
    (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1)
    (S : Finset V) (hS : IsKIndependent G 2 S) : 2 * S.card ≤ Fintype.card V := by
  have hs := uniform_intersections (fun q => (C q).carrier) weight huniform S
  have ht := uniform_intersections (fun q => (C q).carrier) weight huniform Finset.univ
  have he : (∑ q : Q, weight q * ((Finset.univ ∩ (C q).carrier).card : ℚ)) =
      4 * ∑ q : Q, weight q := by
    simp only [Finset.univ_inter,carrier_card]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    norm_num
    ring
  have hb : (∑ q : Q, weight q * ((S ∩ (C q).carrier).card : ℚ)) ≤
      2 * ∑ q : Q, weight q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hc : ((S ∩ (C q).carrier).card : ℚ) ≤ 2 := by
      exact_mod_cast intersection_cap G S hS (C q)
    nlinarith [hweight q]
  rw [he,Finset.card_univ] at ht
  have hh : 2 * (S.card : ℚ) ≤ Fintype.card V := by linarith
  exact_mod_cast hh

/-- The certificate is a bound on the canonical finite maximum. -/
theorem beta_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ)
    (hweight : ∀ q, 0 ≤ weight q)
    (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) :
    2 * beta G 2 ≤ Fintype.card V := by
  obtain ⟨S,hS,hc⟩ := beta_attained G 2
  rw [← hc]
  exact selection_bound G C weight hweight huniform S hS

/-- Bipartiteness supplies attainment at half the order; it supplies no SF bound. -/
theorem beta_exact (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Colorable 2)
    {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ)
    (hweight : ∀ q, 0 ≤ weight q)
    (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) :
    2 * beta G 2 = Fintype.card V := by
  exact le_antisymm (beta_bound G C weight hweight huniform)
    (BipartiteBounds.card_le_two_beta G hG)

end D5.S3.Combinatorics.Graph.StarForming.SquareCapacity
