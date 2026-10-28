/- GID: D5/S3/Combinatorics/Graph/HereditaryFlip/Majority
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HereditaryFlip/Majority
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hereditary finite-support families are majority closed exactly when they are flag. -/

import Mathlib.Data.Finset.Card
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.Tauto

/-! # Majority and flag completion of hereditary finite-support families

The ambient vertex type need not be finite. Empty and singleton faces are
included in the local test, so vertices absent from the family stay absent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.HereditaryFlip.Majority

variable {V : Type*} [DecidableEq V]

/-- The support selected by at least two of three inputs. -/
def majority (A B C : Finset V) : Finset V :=
  (A ∩ B) ∪ (B ∩ C) ∪ (C ∩ A)

/-- Closure under the ternary support majority. -/
def MajorityClosed (K : Set (Finset V)) : Prop :=
  ∀ A ∈ K, ∀ B ∈ K, ∀ C ∈ K, majority A B C ∈ K

/-- Membership is determined by all faces of size at most two, including empty faces. -/
def Flag (K : Set (Finset V)) : Prop :=
  ∀ S : Finset V, (∀ T ⊆ S, T.card ≤ 2 → T ∈ K) → S ∈ K

/-- The family specified by the original empty, singleton and pair constraints. -/
def pairClosure (K : Set (Finset V)) : Set (Finset V) :=
  {S | ∀ T ⊆ S, T.card ≤ 2 → T ∈ K}

private theorem majority_erase (S : Finset V) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    majority (S.erase a) (S.erase b) (S.erase c) = S := by
  ext x
  simp only [majority, Finset.mem_union, Finset.mem_inter, Finset.mem_erase]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all

/-- Every finite support obeying the original two-face constraints
already belongs to any majority-closed containing family, without heredity of that family. -/
private theorem pair_closure_le {K L : Set (Finset V)} (hKL : K ⊆ L)
    (hL : MajorityClosed L) : pairClosure K ⊆ L := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih hS
  by_cases hsmall : S.card ≤ 2
  · exact hKL (hS S Finset.Subset.rfl hsmall)
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge hsmall)
    have herase (x : V) (hx : x ∈ S) : S.erase x ∈ L := by
      apply ih (S.erase x) (Finset.erase_ssubset hx)
      intro T hT hcard
      exact hS T (hT.trans (Finset.erase_subset x S)) hcard
    rw [← majority_erase S hab hac hbc]
    exact hL _ (herase a ha) _ (herase b hb) _ (herase c hc)

private theorem small_subset_majority {T A B C : Finset V}
    (hT : T ⊆ majority A B C) (hcard : T.card ≤ 2) :
    T ⊆ A ∨ T ⊆ B ∨ T ⊆ C := by
  by_cases hzero : T = ∅
  · exact Or.inl (hzero ▸ Finset.empty_subset A)
  have hpair : ∃ x y, T = {x, y} := by
    by_cases htwo : T.card = 2
    · obtain ⟨x, y, _, hxy⟩ := Finset.card_eq_two.mp htwo
      exact ⟨x, y, hxy⟩
    · have hone : T.card = 1 := by
        have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
      exact ⟨x, x, by simpa using hx⟩
  obtain ⟨x, y, rfl⟩ := hpair
  have hx := hT (by simp : x ∈ ({x, y} : Finset V))
  have hy := hT (by simp : y ∈ ({x, y} : Finset V))
  simp only [majority, Finset.mem_union, Finset.mem_inter] at hx hy
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  tauto

private theorem flag_majority_closed {K : Set (Finset V)}
    (hK : IsLowerSet K) (hflag : Flag K) : MajorityClosed K := by
  intro A hA B hB C hC
  apply hflag
  intro T hT hcard
  rcases small_subset_majority hT hcard with h | h | h
  · exact hK h hA
  · exact hK h hB
  · exact hK h hC

/-- A hereditary family of finite supports is majority closed precisely when
its empty, singleton and pair constraints determine every face. -/
theorem majority_closed_iff_flag {K : Set (Finset V)} (hK : IsLowerSet K) :
    MajorityClosed K ↔ Flag K := by
  constructor
  · intro hclosed S hS
    exact pair_closure_le (fun _ h => h) hclosed hS
  · exact flag_majority_closed hK

/-- Pair completion is the least majority-closed family containing a hereditary
family, even when the competing families are not hereditary. -/
theorem pair_closure_is_least {K : Set (Finset V)} (hK : IsLowerSet K) :
    IsLeast {L : Set (Finset V) | K ⊆ L ∧ MajorityClosed L} (pairClosure K) := by
  have hlower : IsLowerSet (pairClosure K) := by
    intro S T hST hT U hUS hcard
    exact hT U (hUS.trans hST) hcard
  have hflag : Flag (pairClosure K) := by
    intro S hS T hTS hcard
    exact hS T hTS hcard T Finset.Subset.rfl hcard
  constructor
  · constructor
    · intro S hS T hTS _
      exact hK hTS hS
    · exact flag_majority_closed hlower hflag
  · intro L hL
    exact pair_closure_le hL.1 hL.2

end D5.S3.Combinatorics.Graph.HereditaryFlip.Majority
