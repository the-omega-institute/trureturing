import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

/-! The deficit-one cut cannot avoid the top triples of the seven heavy coordinates. -/

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
local notation "flip" => BalancedCriticalSpectrum.flip

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- The weight in the last seven coordinates of the nine-cube. -/
def lastSevenWeight (x : Q 9) : ℕ :=
  (univ.filter fun i : Fin 7 => x i.succ.succ = true).card

open Classical in
/-- If every selected vertex has at most three true heavy bits, and their
seven true halves have size 23, the true side of a 31-vertex coordinate
half must contain a top triple. -/
theorem q9_top_triple_on_deficit_one_true_side {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hHalf : ∀ i : Fin 7, (C.filter fun x => x i.succ.succ = true).card = 23)
    (hLow : (C.filter fun x => x (1 : Fin 9) = true).card = 31)
    (hCap : ∀ x ∈ C, lastSevenWeight x ≤ 3) :
    ∃ x ∈ C, x (1 : Fin 9) = true ∧ lastSevenWeight x = 3 := by
  classical
  by_contra! hno
  let T := C.filter fun x => lastSevenWeight x = 3
  let L := C.filter fun x => x (1 : Fin 9) = false
  have htotal : (∑ x ∈ C, lastSevenWeight x) = 161 := by
    simp only [lastSevenWeight, card_filter]
    rw [sum_comm]
    have hn (i : Fin 7) :
        (∑ x ∈ C, if x i.succ.succ = true then (1 : ℕ) else 0) = 23 := by
      exact (card_filter _ _).symm.trans (hHalf i)
    simp [hn]
  have hpoint : ∀ x ∈ C, lastSevenWeight x ≤ 2 + if lastSevenWeight x = 3 then 1 else 0 := by
    intro x hx
    have h := hCap x hx
    split <;> omega
  have hupper := sum_le_sum hpoint
  rw [sum_add_distrib, sum_const, hC, nsmul_eq_mul, ← card_filter] at hupper
  change (∑ x ∈ C, lastSevenWeight x) ≤ 66 * 2 + T.card at hupper
  have hT : 29 ≤ T.card := by omega
  have hsub : T ⊆ L := by
    intro x hx
    obtain ⟨hxC, hxT⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hxC,
      Bool.eq_false_of_not_eq_true (fun h => hno x hxC h hxT)⟩
  have hL : L.card = 35 := by
    have h := card_filter_add_card_filter_not (s := C) (fun x => x (1 : Fin 9) = true)
    have he : C.filter (fun x => ¬ x (1 : Fin 9) = true) = L := by
      ext x
      cases hx : x (1 : Fin 9) <;> simp [L, hx]
    rw [he, hLow, hC] at h
    omega
  have hE : (C.filter fun x => x (1 : Fin 9) = false ∧ flip x 1 ∈ C) ⊆ L \ T := by
    intro x hx
    obtain ⟨hxC, hxL, hflip⟩ := mem_filter.mp hx
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hxC, hxL⟩, ?_⟩
    intro hxT
    have hsame : lastSevenWeight (flip x 1) = lastSevenWeight x := by
      unfold lastSevenWeight
      apply congrArg Finset.card
      apply Finset.ext
      intro i
      have hne : i.succ.succ ≠ (1 : Fin 9) := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hval : flip x 1 i.succ.succ = x i.succ.succ :=
        Function.update_of_ne hne _ _
      simp only [Finset.mem_filter, mem_univ, true_and, hval]
    have ht : lastSevenWeight (flip x 1) = 3 := hsame.trans (mem_filter.mp hxT).2
    have hb1 : flip x 1 1 = true := by
      simp [BalancedCriticalSpectrum.flip_apply_same, hxL]
    exact hno (flip x 1) hflip hb1 ht
  have hbound := card_le_card hE
  change directionEdges C (1 : Fin 9) ≤ (L \ T).card at hbound
  have hdir := direction_edge_count (d := 3) C hr hb (1 : Fin 9)
  rw [card_sdiff_of_subset hsub, hL] at hbound
  omega

#print axioms q9_top_triple_on_deficit_one_true_side

end D5.S3.Combinatorics.Graph.HypercubeCritical
