/- GID: D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact rectangular weak two-metric dimensions. -/

import D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimensionCore
import D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimensionLower
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.IntervalCases

namespace D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimension

open Function

private def leftCount {α β : Type*} [DecidableEq α] (S : Finset (α × β)) (a : α) : ℕ :=
  (S.filter (fun e => e.1 = a)).card

private def rightCount {α β : Type*} [DecidableEq β] (S : Finset (α × β)) (b : β) : ℕ :=
  (S.filter (fun e => e.2 = b)).card

private def Good {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) : Prop :=
  (∀ a, 1 ≤ leftCount S a) ∧ (∀ b, 1 ≤ rightCount S b) ∧
  ∀ e ∈ S, 3 ≤ leftCount S e.1 + rightCount S e.2

private def join {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ]
    (S : Finset (α × β)) (T : Finset (γ × δ)) : Finset ((α ⊕ γ) × (β ⊕ δ)) :=
  S.map (Embedding.inl.prodMap Embedding.inl) ∪
  T.map (Embedding.inr.prodMap Embedding.inr)

private theorem join_disjoint {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ)) :
    Disjoint (S.map (Embedding.inl.prodMap Embedding.inl))
      (T.map (Embedding.inr.prodMap Embedding.inr)) := by
  apply Finset.disjoint_left.mpr
  intro e hs ht
  obtain ⟨s, _, rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨t, _, h⟩ := Finset.mem_map.mp ht
  have hh : Sum.inr t.1 = Sum.inl s.1 := congrArg (fun e => e.1) h
  cases hh

private theorem join_card {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ)) :
    (join S T).card = S.card + T.card := by
  simp [join, Finset.card_union_of_disjoint (join_disjoint S T)]

private theorem join_left_inl {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ)) (a : α) :
    leftCount (join S T) (Sum.inl a) = leftCount S a := by
  simp [leftCount, join, Finset.filter_union, Finset.filter_map, Function.comp_def]

private theorem join_left_inr {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ)) (a : γ) :
    leftCount (join S T) (Sum.inr a) = leftCount T a := by
  simp [leftCount, join, Finset.filter_union, Finset.filter_map, Function.comp_def]

private theorem join_right_inl {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ)) (b : β) :
    rightCount (join S T) (Sum.inl b) = rightCount S b := by
  simp [rightCount, join, Finset.filter_union, Finset.filter_map, Function.comp_def]

private theorem join_right_inr {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (S : Finset (α × β)) (T : Finset (γ × δ)) (b : δ) :
    rightCount (join S T) (Sum.inr b) = rightCount T b := by
  simp [rightCount, join, Finset.filter_union, Finset.filter_map, Function.comp_def]

private theorem good_join {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] {S : Finset (α × β)} {T : Finset (γ × δ)}
    (hS : Good S) (hT : Good T) : Good (join S T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    cases a with
    | inl a => simpa [join_left_inl] using hS.1 a
    | inr a => simpa [join_left_inr] using hT.1 a
  · intro b
    cases b with
    | inl b => simpa [join_right_inl] using hS.2.1 b
    | inr b => simpa [join_right_inr] using hT.2.1 b
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp he
      simpa [join_left_inl, join_right_inl] using hS.2.2 s hs
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp he
      simpa [join_left_inr, join_right_inr] using hT.2.2 s hs

private theorem good_map {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] (f : α ≃ γ) (g : β ≃ δ)
    {S : Finset (α × β)} (hS : Good S) :
    Good (S.map (f.toEmbedding.prodMap g.toEmbedding)) := by
  have hl (a : α) : leftCount (S.map (f.toEmbedding.prodMap g.toEmbedding)) (f a) =
      leftCount S a := by
    simp [leftCount, Finset.filter_map, Function.comp_def]
  have hr (b : β) : rightCount (S.map (f.toEmbedding.prodMap g.toEmbedding)) (g b) =
      rightCount S b := by
    simp [rightCount, Finset.filter_map, Function.comp_def]
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨a, rfl⟩ := f.surjective a
    simpa [hl] using hS.1 a
  · intro b
    obtain ⟨b, rfl⟩ := g.surjective b
    simpa [hr] using hS.2.1 b
  · intro e he
    obtain ⟨e, hs, rfl⟩ := Finset.mem_map.mp he
    simpa [hl, hr] using hS.2.2 e hs

private theorem small_design (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hbal₁ : n ≤ 2 * m) (hbal₂ : m ≤ 2 * n) (hN : 3 ≤ n + m) (hsmall : n + m ≤ 5) :
    ∃ S : Finset (Fin n × Fin m), Good S ∧ S.card ≤ (2 * (n + m) + 2) / 3 := by
  have hn5 : n ≤ 5 := by omega
  have hm5 : m ≤ 5 := by omega
  interval_cases n <;> interval_cases m <;> try omega
  all_goals first
  | exact ⟨Finset.univ, by unfold Good leftCount rightCount; decide, by decide⟩
  | exact ⟨{(0,0), (0,1), (1,1)}, by unfold Good leftCount rightCount; decide, by decide⟩
  | exact ⟨{(0,0), (0,1), (1,1), (1,2)}, by unfold Good leftCount rightCount; decide, by decide⟩
  | exact ⟨{(0,0), (1,0), (1,1), (2,1)}, by unfold Good leftCount rightCount; decide, by decide⟩

private theorem balanced_design (N : ℕ) : ∀ n m : ℕ, n + m = N →
    0 < n → 0 < m → n ≤ 2 * m → m ≤ 2 * n → 3 ≤ n + m →
    ∃ S : Finset (Fin n × Fin m), Good S ∧ S.card ≤ (2 * (n + m) + 2) / 3 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro n m hsum hn hm hbal₁ hbal₂ hN
    by_cases hsmall : n + m ≤ 5
    · exact small_design n m hn hm hbal₁ hbal₂ hN hsmall
    by_cases hnm : n ≤ m
    · have hn₂ : 2 ≤ n := by omega
      have hm₃ : 3 ≤ m := by omega
      obtain ⟨S, hS, hcard⟩ := ih ((n-1)+(m-2)) (by omega) (n-1) (m-2) rfl
        (by omega) (by omega) (by omega) (by omega) (by omega)
      let T : Finset (Fin 1 × Fin 2) := Finset.univ
      have hT : Good T := by unfold Good leftCount rightCount T; decide
      let f : Fin (n-1) ⊕ Fin 1 ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
      let g : Fin (m-2) ⊕ Fin 2 ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega))
      refine ⟨(join S T).map (f.toEmbedding.prodMap g.toEmbedding),
        good_map f g (good_join hS hT), ?_⟩
      simp only [Finset.card_map, join_card]
      have ht : T.card = 2 := by decide
      rw [ht]
      omega
    · have hm₂ : 2 ≤ m := by omega
      have hn₃ : 3 ≤ n := by omega
      obtain ⟨S, hS, hcard⟩ := ih ((n-2)+(m-1)) (by omega) (n-2) (m-1) rfl
        (by omega) (by omega) (by omega) (by omega) (by omega)
      let T : Finset (Fin 2 × Fin 1) := Finset.univ
      have hT : Good T := by unfold Good leftCount rightCount T; decide
      let f : Fin (n-2) ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
      let g : Fin (m-1) ⊕ Fin 1 ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega))
      refine ⟨(join S T).map (f.toEmbedding.prodMap g.toEmbedding),
        good_map f g (good_join hS hT), ?_⟩
      simp only [Finset.card_map, join_card]
      have ht : T.card = 2 := by decide
      rw [ht]
      omega

private theorem adjacent_mod_ne (a m : ℕ) (hm : 2 ≤ m) : a % m ≠ (a+1) % m := by
  have hlt := Nat.mod_lt a (by omega : 0 < m)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m)]
  by_cases h : a % m + 1 < m
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : a % m + 1 = m := by omega
    rw [he, Nat.mod_self]
    omega

private def cyclicEdges {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    Fin (2 * (n-1)) ↪ Fin n × Fin m where
  toFun q := (⟨q.val / 2 + 1, by have := q.isLt; omega⟩,
    ⟨q.val % m, Nat.mod_lt _ (by omega)⟩)
  inj' := by
    intro q q' h
    have hr : q.val / 2 = q'.val / 2 := by
      have he := congrArg (fun e => e.1.val) h
      simpa using he
    have hc : q.val % m = q'.val % m := congrArg (fun e => e.2.val) h
    apply Fin.ext
    by_contra hq
    have hh : q.val = q'.val + 1 ∨ q'.val = q.val + 1 := by omega
    rcases hh with hh | hh
    · exact adjacent_mod_ne q'.val m hm (hh ▸ hc.symm)
    · exact adjacent_mod_ne q.val m hm (hh ▸ hc)

private theorem cyclic_row {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (i : Fin n) :
    leftCount (Finset.univ.map (cyclicEdges hn hm)) i = if i.val = 0 then 0 else 2 := by
  simp only [leftCount, Finset.filter_map, Finset.card_map]
  by_cases hi : i.val = 0
  · have he : (Finset.univ.filter (fun q : Fin (2*(n-1)) =>
        (cyclicEdges hn hm q).1 = i)) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      have hv := congrArg Fin.val h
      change q.val / 2 + 1 = i.val at hv
      omega
    simpa [Function.comp_def, hi] using congrArg Finset.card he
  · let q₀ : Fin (2*(n-1)) := ⟨2*(i.val-1), by have := i.isLt; omega⟩
    let q₁ : Fin (2*(n-1)) := ⟨2*(i.val-1)+1, by have := i.isLt; omega⟩
    have hq : q₀ ≠ q₁ := by intro h; have := congrArg Fin.val h; dsimp [q₀,q₁] at this; omega
    have he : (Finset.univ.filter (fun q : Fin (2*(n-1)) =>
        (cyclicEdges hn hm q).1 = i)) = {q₀,q₁} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      change (⟨q.val / 2 + 1, _⟩ : Fin n) = i ↔ q = q₀ ∨ q = q₁
      simp only [Fin.ext_iff]
      dsimp [q₀,q₁]
      omega
    simpa [Function.comp_def, hi, hq] using congrArg Finset.card he

private theorem cyclic_column {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcover : m ≤ 2*(n-1)) (j : Fin m) :
    1 ≤ rightCount (Finset.univ.map (cyclicEdges hn hm)) j := by
  let q : Fin (2*(n-1)) := ⟨j.val, lt_of_lt_of_le j.isLt hcover⟩
  have he : (cyclicEdges hn hm q).2 = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  have hm' : cyclicEdges hn hm q ∈ Finset.univ.map (cyclicEdges hn hm) :=
    Finset.mem_map.mpr ⟨q, Finset.mem_univ q, rfl⟩
  exact Finset.one_le_card.mpr ⟨_, Finset.mem_filter.mpr ⟨hm',he⟩⟩

/-- A spanning bipartite forest with no isolated vertices or isolated edges gives the
ceiling upper bound. Three new vertices require only two new landmarks. -/
theorem ceiling_upper (n m : ℕ) (hn : 4 ≤ n) (hnm : n < m) (hmn : m < 2*n-2) :
    ∃ S : Finset (Fin n × Fin m), IsWeakResolving 2 S ∧
      S.card ≤ (2*(n+m)+2)/3 := by
  obtain ⟨S, hS, hcard⟩ := balanced_design (n+m) n m rfl
    (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨S, weak_of_degrees S ?_ ?_ ?_, hcard⟩
  · simpa [rowDegree, leftCount] using hS.1
  · simpa [colDegree, rightCount] using hS.2.1
  · intro i j he
    simpa [rowDegree, colDegree, leftCount, rightCount] using hS.2.2 (i,j) he

/-- Leaving a row empty and placing two cyclically consecutive landmarks in each
remaining row gives the second upper bound. -/
theorem empty_row_upper (n m : ℕ) (hn : 4 ≤ n) (hnm : n < m) (hmn : m < 2*n-2) :
    ∃ S : Finset (Fin n × Fin m), IsWeakResolving 2 S ∧ S.card ≤ 2*n-2 := by
  have hn₂ : 2 ≤ n := by omega
  have hm₂ : 2 ≤ m := by omega
  let S := Finset.univ.map (cyclicEdges hn₂ hm₂)
  have hr (i : Fin n) : rowDegree S i = if i.val = 0 then 0 else 2 :=
    cyclic_row hn₂ hm₂ i
  have hc (j : Fin m) : 1 ≤ colDegree S j :=
    cyclic_column hn₂ hm₂ (by omega) j
  have hedge (i : Fin n) (j : Fin m) (h : (i,j) ∈ S) : rowDegree S i = 2 := by
    obtain ⟨q, _, he⟩ := Finset.mem_map.mp h
    have hv := congrArg (fun e => e.1.val) he
    change q.val / 2 + 1 = i.val at hv
    rw [hr, if_neg (by omega)]
  refine ⟨S, weak_of_pair_degrees S ?_ ?_ ?_, ?_⟩
  · intro i i' hii
    have hi0 : ¬(i.val = 0 ∧ i'.val = 0) := by
      rintro ⟨hi,hi'⟩
      exact hii (Fin.ext (hi.trans hi'.symm))
    rw [hr,hr]
    split_ifs <;> omega
  · intro j j' _
    have := hc j
    have := hc j'
    omega
  · intro i i' j j' ha hb _ _
    rw [hedge i j ha, hedge i' j' hb]
    have := hc j
    have := hc j'
    omega
  · simp only [S, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    omega

/-- The remaining strictly rectangular weak two-metric dimensions.
In natural-number arithmetic, `⌈2(n+m)/3⌉ = (2*(n+m)+2)/3`. -/
def claim : Prop := ∀ n m : ℕ, 4 ≤ n → n < m → m < 2 * n - 2 →
  wdim n m 2 = min ((2 * (n + m) + 2) / 3) (2 * n - 2)

/-- The incidence lower bound is attained by one of the two explicit constructions. -/
theorem result : claim := by
  intro n m hn hnm hmn
  apply le_antisymm
  · obtain ⟨S, hS, hc⟩ := ceiling_upper n m hn hnm hmn
    obtain ⟨T, hT, ht⟩ := empty_row_upper n m hn hnm hmn
    exact le_min ((wdim_le_card S 2 hS).trans hc) ((wdim_le_card T 2 hT).trans ht)
  · apply le_wdim_two
    intro S hS
    exact lower_bound S hS hn hnm

end D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimension
