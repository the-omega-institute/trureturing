/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactAxisOrbits
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactAxisOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Axis permutations reduce shared nine-cube contact triples to three cases. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
import Mathlib.Logic.Equiv.Fintype

/-! The three orbits of a distance-three contact with a shared occupied flip. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactAxisOrbits

open Finset

private abbrev Axis := Fin 9

private def axisClass (t a b : Bool) : Fin 5 :=
  if t then 0 else if a then (if b then 1 else 2) else if b then 3 else 4

/-- In the canonical coordinates, the two contact vertices differ on axes
zero through two. The second support uses axes three through five. -/
def canonicalDifference (i : Axis) : Bool := decide (i.val < 3)

def canonicalRight (i : Axis) : Bool := decide (3 ≤ i.val ∧ i.val < 6)

def canonicalLeft (k : Fin 3) (i : Axis) : Bool :=
  decide ((3 ≤ i.val ∧ i.val < 4 + k.val) ∨ (6 ≤ i.val ∧ i.val < 8 - k.val))

private def canonicalClass (k : Fin 3) (i : Axis) : Fin 5 :=
  axisClass (canonicalDifference i) (canonicalLeft k i) (canonicalRight i)

private def fiberSize (k : Fin 3) (c : Fin 5) : ℕ :=
  ![3, k.val + 1, 2 - k.val, 2 - k.val, k.val + 1] c

private theorem canonical_card (k : Fin 3) (c : Fin 5) :
    (univ.filter fun i => canonicalClass k i = c).card = fiberSize k c := by
  fin_cases k <;> fin_cases c <;> decide

private theorem equiv_of_equal_fibers (f g : Axis → Fin 5)
    (h : ∀ c, (univ.filter fun i => f i = c).card =
      (univ.filter fun i => g i = c).card) :
    ∃ σ : Equiv.Perm Axis, ∀ i, g (σ i) = f i := by
  classical
  have card_fiber (v : Axis → Fin 5) (c : Fin 5) :
      Fintype.card {i : Axis // v i = c} = (univ.filter fun i => v i = c).card :=
    Fintype.card_of_subtype _ (by intro i; simp)
  let e (c : Fin 5) : {i : Axis // f i = c} ≃ {i : Axis // g i = c} :=
    Fintype.equivOfCardEq (by rw [card_fiber f c, card_fiber g c, h c])
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private def actualClass (T A B : Finset Axis) (i : Axis) : Fin 5 :=
  axisClass (decide (i ∈ T)) (decide (i ∈ A)) (decide (i ∈ B))

private theorem class_bits {T A B : Finset Axis} {k : Fin 3} {i j : Axis}
    (hTA : Disjoint T A) (hTB : Disjoint T B)
    (h : actualClass T A B j = canonicalClass k i) :
    ((j ∈ T) ↔ canonicalDifference i = true) ∧
    ((j ∈ A) ↔ canonicalLeft k i = true) ∧
    ((j ∈ B) ↔ canonicalRight i = true) := by
  by_cases ht : j ∈ T <;> by_cases ha : j ∈ A <;> by_cases hb : j ∈ B
  all_goals try exact (disjoint_left.mp hTA ht ha).elim
  all_goals try exact (disjoint_left.mp hTB ht hb).elim
  all_goals fin_cases k <;> fin_cases i <;>
    simp_all [actualClass, canonicalClass, canonicalDifference, canonicalLeft, canonicalRight, axisClass]

open Classical in
/-- The permutation group on the nine axes has exactly the three canonical
patterns for the difference triple and the two occupied triples with a
nonempty intersection. The size of the intersection selects the pattern. -/
theorem exists_axis_permutation {T A B : Finset Axis}
    (hT : T.card = 3) (hA : A.card = 3) (hB : B.card = 3)
    (hTA : Disjoint T A) (hTB : Disjoint T B) (hshare : (A ∩ B).Nonempty) :
    ∃ k : Fin 3, ∃ σ : Equiv.Perm Axis,
      (A ∩ B).card = k.val + 1 ∧ ∀ i,
      ((σ i ∈ T) ↔ canonicalDifference i = true) ∧
      ((σ i ∈ A) ↔ canonicalLeft k i = true) ∧
      ((σ i ∈ B) ↔ canonicalRight i = true) := by
  let k : Fin 3 := ⟨(A ∩ B).card - 1, by
    have := card_le_card (inter_subset_left (s₁ := A) (s₂ := B))
    omega⟩
  have hk : (A ∩ B).card = k.val + 1 := by
    change (A ∩ B).card = (A ∩ B).card - 1 + 1
    have := card_pos.mpr hshare
    omega
  have hTU : Disjoint T (A ∪ B) := disjoint_left.mpr fun _ ht h =>
    (mem_union.mp h).elim (disjoint_left.mp hTA ht) (disjoint_left.mp hTB ht)
  have hcards :
      (A \ B).card = 2 - k.val ∧
      (B \ A).card = 2 - k.val ∧
      ((univ : Finset Axis) \ (T ∪ (A ∪ B))).card = k.val + 1 := by
    have hsum := card_union_add_card_inter A B
    rw [hA, hB] at hsum
    have ha := card_sdiff_add_card_inter A B
    have hb := card_sdiff_add_card_inter B A
    rw [inter_comm B A, hB] at hb
    rw [hA] at ha
    rw [card_univ_sdiff, Fintype.card_fin, card_union_of_disjoint hTU, hT]
    omega
  have hf (c : Fin 5) : (univ.filter fun i => actualClass T A B i = c).card = fiberSize k c := by
    have hset : (univ.filter fun i => actualClass T A B i = c) =
        ![T, A ∩ B, A \ B, B \ A, univ \ (T ∪ (A ∪ B))] c := by
      ext i
      by_cases ht : i ∈ T <;> by_cases ha : i ∈ A <;> by_cases hb : i ∈ B
      all_goals try exact (disjoint_left.mp hTA ht ha).elim
      all_goals try exact (disjoint_left.mp hTB ht hb).elim
      all_goals fin_cases c <;> simp [actualClass, axisClass, ht, ha, hb]
    rw [hset]
    fin_cases c
    · simpa [fiberSize] using hT
    · simpa [fiberSize] using hk
    · simpa [fiberSize] using hcards.1
    · simpa [fiberSize] using hcards.2.1
    · simpa [fiberSize] using hcards.2.2
  obtain ⟨σ, hσ⟩ := equiv_of_equal_fibers (canonicalClass k) (actualClass T A B)
    (fun c => (canonical_card k c).trans (hf c).symm)
  exact ⟨k, σ, hk, fun i => class_bits hTA hTB (hσ i)⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactAxisOrbits
