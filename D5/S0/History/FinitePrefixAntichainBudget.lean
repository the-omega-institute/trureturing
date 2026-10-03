/- GID: D5/S0/History/FinitePrefixAntichainBudget
   generality: G
   mirror-B: D5/B/S0/History/FinitePrefixAntichainBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite prefix antichains inherit a root budget from finite local child budgets. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Image

namespace D5.S0.History.FinitePrefixAntichainBudget

/-- A finite prefix antichain is bounded by the root whenever every finite
selection of children is bounded by its parent. No finite alphabet is needed. -/
theorem result {E V : Type*} [DecidableEq E] [AddCommMonoid V]
    [Preorder V] [IsOrderedAddMonoid V] (m : List E → V)
    (localBudget : ∀ h (C : Finset E), ∑ a ∈ C, m (h ++ [a]) ≤ m h)
    (K : Finset (List E))
    (antichain : ∀ h ∈ K, ∀ k ∈ K, h.IsPrefix k → h = k) :
    ∑ h ∈ K, m h ≤ m [] := by
  classical
  have bounded : ∀ n : ℕ, ∀ (m : List E → V),
      (∀ h (C : Finset E), ∑ a ∈ C, m (h ++ [a]) ≤ m h) →
      ∀ K : Finset (List E),
      (∀ h ∈ K, ∀ k ∈ K, h.IsPrefix k → h = k) →
      (∀ h ∈ K, h.length ≤ n) → ∑ h ∈ K, m h ≤ m [] := by
    intro n
    induction n with
    | zero =>
      intro m hm K ha hn
      by_cases he : K = ∅
      · simpa [he] using hm [] ∅
      · obtain ⟨h, hh⟩ := Finset.nonempty_iff_ne_empty.mpr he
        have hK : K = {[]} := by
          ext k
          simp only [Finset.mem_singleton]
          constructor
          · intro hk
            simpa using hn k hk
          · intro hk
            subst k
            have hz : h = [] := by simpa using hn h hh
            simpa [hz] using hh
        simp [hK]
    | succ n ih =>
      intro m hm K ha hn
      by_cases hr : [] ∈ K
      · have hK : K = {[]} := by
          ext k
          simp only [Finset.mem_singleton]
          constructor
          · intro hk
            exact (ha [] hr k hk List.nil_prefix).symm
          · rintro rfl
            exact hr
        simp [hK]
      · let C : Finset E := K.biUnion (fun h => (h.take 1).toFinset)
        let T (a : E) : Finset (List E) := (K.image List.tail).filter (fun t => a :: t ∈ K)
        have ht (a : E) (t : List E) : t ∈ T a ↔ a :: t ∈ K := by
          simp only [T, Finset.mem_filter, Finset.mem_image]
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨⟨a :: t, h, rfl⟩, h⟩
        have hu : K = C.biUnion (fun a => (T a).image (List.cons a)) := by
          ext h
          simp only [Finset.mem_biUnion, Finset.mem_image]
          constructor
          · intro hh
            cases h with
            | nil => exact (hr hh).elim
            | cons a t =>
              refine ⟨a, ?_, t, (ht a t).mpr hh, rfl⟩
              exact Finset.mem_biUnion.mpr ⟨a :: t, hh, by simp⟩
          · rintro ⟨a, _, t, ht', rfl⟩
            exact (ht a t).mp ht'
        have hd : (C : Set E).PairwiseDisjoint (fun a => (T a).image (List.cons a)) := by
          intro a _ b _ hab
          apply Finset.disjoint_left.mpr
          intro t hta htb
          obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hta
          obtain ⟨u, _, heq⟩ := Finset.mem_image.mp htb
          exact hab (List.cons.inj heq).1.symm
        calc
          ∑ h ∈ K, m h = ∑ a ∈ C, ∑ t ∈ T a, m (a :: t) := by
            rw [hu, Finset.sum_biUnion hd]
            apply Finset.sum_congr rfl
            intro a _
            exact Finset.sum_image (fun _ _ _ _ h => List.cons.inj h |>.2)
          _ ≤ ∑ a ∈ C, m [a] := by
            apply Finset.sum_le_sum
            intro a _
            apply ih (fun t => m (a :: t))
            · intro h B
              simpa using hm (a :: h) B
            · intro s hs t ht' hp
              exact (List.cons.inj (ha (a :: s) ((ht a s).mp hs)
                (a :: t) ((ht a t).mp ht') (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))).2
            · intro t ht'
              have := hn (a :: t) ((ht a t).mp ht')
              simpa using this
          _ ≤ m [] := by simpa using hm [] C
  exact bounded (K.sup List.length) m localBudget K antichain
    (fun h hh => Finset.le_sup (f := List.length) hh)

end D5.S0.History.FinitePrefixAntichainBudget
