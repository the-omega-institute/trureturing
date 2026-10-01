/- GID: D5/S0/History/WellFoundedLeafMassConservation
   generality: G
   mirror-B: D5/B/S0/History/WellFoundedLeafMassConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Well-founded countably branching trees conserve mass at their leaves. -/

import Mathlib.Data.List.Infix
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace D5.S0.History.WellFoundedLeafMassConservation

open Classical in
/-- Local conservation on nonleaves of a well-founded tree implies conservation
at all leaves, including infinite mass and unbounded finite branch lengths. -/
theorem result {E : Type*} [Countable E] (T : Set (List E))
    (root : [] ∈ T)
    (prefixclosed : ∀ ⦃h k : List E⦄, h.IsPrefix k → k ∈ T → h ∈ T)
    (m : List E → ENNReal)
    (wf : WellFounded (fun k h : List E =>
      k ∈ T ∧ h ∈ T ∧ ∃ a : E, k = h ++ [a]))
    (localMass : ∀ h ∈ T, ¬ (h ∈ T ∧ ∀ a : E, h ++ [a] ∉ T) →
      m h = ∑' a : E, if h ++ [a] ∈ T then m (h ++ [a]) else 0) :
    (∑' l : {h : List E // h ∈ T ∧ ∀ a : E, h ++ [a] ∉ T}, m l.val) = m [] := by
  classical
  let leaf := fun h : List E => h ∈ T ∧ ∀ a : E, h ++ [a] ∉ T
  let mass := fun h : List E => if leaf h then m h else 0
  let split : (Unit ⊕ (E × List E)) ≃ List E :=
    { toFun := fun x => match x with
        | Sum.inl _ => []
        | Sum.inr p => p.1 :: p.2
      invFun := fun l => match l with
        | [] => Sum.inl Unit.unit
        | a :: t => Sum.inr (a, t)
      left_inv := by
        intro x
        rcases x with u | ⟨a, t⟩
        · cases u; rfl
        · rfl
      right_inv := by intro l; cases l <;> rfl }
  have partition (f : List E → ENNReal) :
      (∑' t, f t) = f [] + ∑' a : E, ∑' t : List E, f (a :: t) := by
    rw [← split.tsum_eq f, ENNReal.summable.tsum_sum ENNReal.summable]
    simp only [split, Equiv.coe_fn_mk]
    rw [ENNReal.tsum_prod']
    simp
  have invariant : ∀ h : List E, h ∈ T → (∑' t : List E, mass (h ++ t)) = m h := by
    intro h
    induction h using wf.induction with
    | h h ih =>
      intro ht
      by_cases hl : leaf h
      · rw [tsum_eq_single []]
        · simp [mass, hl]
        · intro t htn
          have hn : ¬ leaf (h ++ t) := by
            intro hd
            cases t with
            | nil => exact htn rfl
            | cons a t =>
              apply hl.2 a
              apply prefixclosed (k := h ++ a :: t) _ hd.1
              exact ⟨t, by simp⟩
          simp [mass, hn]
      · rw [partition]
        have hz : mass (h ++ []) = 0 := by simp [mass, hl]
        rw [hz, zero_add, localMass h ht hl]
        apply tsum_congr
        intro a
        by_cases hc : h ++ [a] ∈ T
        · simp only [if_pos hc]
          simpa only [List.append_assoc, List.singleton_append] using
            ih (h ++ [a]) ⟨hc, ht, a, rfl⟩ hc
        · rw [if_neg hc]
          trans ∑' _t : List E, (0 : ENNReal)
          · apply tsum_congr
            intro t
            have hn : ¬ leaf (h ++ a :: t) := by
              intro hd
              exact hc (prefixclosed ⟨t, by simp⟩ hd.1)
            simp [mass, hn]
          · simp
  have atRoot := invariant [] root
  change (∑' l : {h : List E | leaf h}, m l.val) = m []
  rw [tsum_subtype]
  calc
    (∑' x : List E, {h : List E | leaf h}.indicator m x) =
        ∑' t : List E, mass ([] ++ t) := by
      apply tsum_congr
      intro t
      by_cases ht : leaf t <;> simp [Set.indicator, mass, ht]
    _ = m [] := atRoot

end D5.S0.History.WellFoundedLeafMassConservation
