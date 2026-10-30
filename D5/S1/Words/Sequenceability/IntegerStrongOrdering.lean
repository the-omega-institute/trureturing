/- GID: D5/S1/Words/Sequenceability/IntegerStrongOrdering
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/IntegerStrongOrdering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integer orders without proper zero-sum intervals via positive-prefix recursion. -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.TakeDrop

/-! Two-sided integer sequencing by the simultaneous positive-prefix construction of Kravitz. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.IntegerStrongOrdering

private def Separated (p n : List ℤ) : Prop :=
  ∀ i ≤ p.length, ∀ j ≤ n.length,
    (p.take i).sum = (n.take j).sum →
      (i = 0 ∧ j = 0) ∨ (i = p.length ∧ j = n.length)

private theorem prefix_lt (l : List ℤ) (hl : ∀ x ∈ l, 0 < x)
    {i j : ℕ} (hij : i < j) (hj : j ≤ l.length) :
    (l.take i).sum < (l.take j).sum := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep : (l.take j).sum < (l.take (j + 1)).sum := by
      rw [List.sum_take_succ l j (by omega)]
      have := hl l[j] (List.getElem_mem (by omega))
      omega
    by_cases hi : i = j
    · simpa [hi] using hstep
    · exact lt_trans (ih (by omega) (by omega)) hstep

private theorem separated_positive (P N : Finset ℤ)
    (hP : ∀ x ∈ P, 0 < x) (hN : ∀ x ∈ N, 0 < x) :
    ∃ p n : List ℤ, p.Perm P.toList ∧ n.Perm N.toList ∧ Separated p n := by
  classical
  suffices all : ∀ t : ℕ, ∀ P N : Finset ℤ,
      P.card + N.card = t → (∀ x ∈ P, 0 < x) → (∀ x ∈ N, 0 < x) →
      ∃ p n : List ℤ, p.Perm P.toList ∧ n.Perm N.toList ∧ Separated p n by
    exact all _ P N rfl hP hN
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have ordered : ∀ P N : Finset ℤ, P.card + N.card = t →
        (∀ x ∈ P, 0 < x) → (∀ x ∈ N, 0 < x) →
        (∑ x ∈ N, x) ≤ (∑ x ∈ P, x) →
        ∃ p n : List ℤ, p.Perm P.toList ∧ n.Perm N.toList ∧ Separated p n := by
      intro P N ht hp hn hsum
      by_cases hc : P.card ≤ 1
      · refine ⟨P.toList, N.toList, .refl _, .refl _, ?_⟩
        intro i hi j hj he
        have hpl : P.toList.length ≤ 1 := by simpa using hc
        have hnp : ∀ x ∈ N.toList, 0 < x := by simpa using hn
        by_cases hiz : i = 0
        · left
          refine ⟨hiz, ?_⟩
          by_contra hjz
          have hh := prefix_lt N.toList hnp (i := 0) (j := j) (by omega) hj
          simp [hiz] at he
          simp only [List.take_zero, List.sum_nil] at hh
          omega
        · right
          have hil : i = P.toList.length := by omega
          refine ⟨hil, ?_⟩
          by_contra hjl
          have hh := prefix_lt N.toList hnp (i := j) (j := N.toList.length)
            (by omega) (le_refl _)
          simp only [List.take_length, Finset.sum_toList] at hh
          simp only [hil, List.take_length, Finset.sum_toList] at he
          omega
      · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
        have hex : ∃ x ∈ P, (∑ y ∈ P.erase x, y) ≠ ∑ y ∈ N, y := by
          by_cases hbad : (∑ y ∈ P.erase a, y) = ∑ y ∈ N, y
          · refine ⟨b, hb, ?_⟩
            intro hbadb
            have ha' := Finset.sum_erase_add (s := P) (fun x : ℤ => x) ha
            have hb' := Finset.sum_erase_add (s := P) (fun x : ℤ => x) hb
            exact hab (by omega)
          · exact ⟨a, ha, hbad⟩
        obtain ⟨x, hx, hne⟩ := hex
        obtain ⟨p, n, hpp, hnn, hsep⟩ := ih ((P.erase x).card + N.card)
          (by have := Finset.card_erase_lt_of_mem hx; omega) (P.erase x) N rfl
          (fun y hy => hp y (Finset.mem_of_mem_erase hy)) hn
        have hpp' : (p ++ [x]).Perm P.toList := by
          have hpins := Finset.toList_insert (Finset.notMem_erase x P)
          rw [Finset.insert_erase hx] at hpins
          exact ((List.perm_append_comm).trans (List.Perm.cons x hpp)).trans hpins.symm
        have hnp : ∀ y ∈ n, 0 < y := by
          intro y hy
          exact hn y (Finset.mem_toList.mp (hnn.mem_iff.mp hy))
        have hsump : (p ++ [x]).sum = ∑ y ∈ P, y := by
          simpa using hpp'.sum_eq
        have hsumn : n.sum = ∑ y ∈ N, y := by simpa using hnn.sum_eq
        have hsump' : p.sum = ∑ y ∈ P.erase x, y := by simpa using hpp.sum_eq
        refine ⟨p ++ [x], n, hpp', hnn, ?_⟩
        intro i hi j hj he
        by_cases hip : i ≤ p.length
        · rw [List.take_append_of_le_length hip] at he
          rcases hsep i hip j hj he with hzero | hfull
          · exact Or.inl hzero
          · obtain ⟨rfl, rfl⟩ := hfull
            simp only [List.take_length] at he
            exact (hne (by omega)).elim
        · have hil : i = (p ++ [x]).length := by
            simp only [List.length_append, List.length_singleton] at hi ⊢
            omega
          right
          refine ⟨hil, ?_⟩
          by_contra hjl
          have hh := prefix_lt n hnp (i := j) (j := n.length) (by omega) (le_refl _)
          rw [hil, List.take_length] at he
          simp only [List.take_length] at hh
          omega
    intro P N ht hp hn
    by_cases hsum : (∑ x ∈ N, x) ≤ (∑ x ∈ P, x)
    · exact ordered P N ht hp hn hsum
    · obtain ⟨n, p, hnn, hpp, hs⟩ := ordered N P (by omega) hn hp (by omega)
      refine ⟨p, n, hpp, hnn, ?_⟩
      intro i hi j hj he
      rcases hs j hj i hi he.symm with hz | hf
      · exact Or.inl ⟨hz.2, hz.1⟩
      · exact Or.inr ⟨hf.2, hf.1⟩

private theorem first_prefix (p n : List ℤ) {i : ℕ} (hi : i ≤ p.length) :
    ((p.reverse ++ n.map (-·)).take i).sum = p.sum - (p.take (p.length - i)).sum := by
  rw [List.take_append_of_le_length (by simpa using hi), List.take_reverse,
    List.sum_reverse]
  have := List.sum_take_add_sum_drop p (p.length - i)
  omega

private theorem second_prefix (p n : List ℤ) {i : ℕ} (hi : p.length ≤ i) :
    ((p.reverse ++ n.map (-·)).take i).sum = p.sum - (n.take (i - p.length)).sum := by
  rw [List.take_append, List.take_of_length_le (by simpa using hi), List.sum_append]
  simp [← List.map_take, List.sum_neg, sub_eq_add_neg]

private theorem collision_endpoints (p n : List ℤ)
    (hp : ∀ x ∈ p, 0 < x) (hn : ∀ x ∈ n, 0 < x) (hs : Separated p n)
    {i j : ℕ} (hij : i < j) (hj : j ≤ (p.reverse ++ n.map (-·)).length)
    (he : ((p.reverse ++ n.map (-·)).take i).sum =
      ((p.reverse ++ n.map (-·)).take j).sum) :
    i = 0 ∧ j = (p.reverse ++ n.map (-·)).length := by
  have hlen : (p.reverse ++ n.map (-·)).length = p.length + n.length := by simp
  by_cases hjp : j ≤ p.length
  · rw [first_prefix p n (by omega), first_prefix p n hjp] at he
    have hh := prefix_lt p hp (i := p.length - j) (j := p.length - i)
      (by omega) (by omega)
    omega
  · by_cases hip : i ≤ p.length
    · rw [first_prefix p n hip, second_prefix p n (by omega)] at he
      have he' : (p.take (p.length - i)).sum = (n.take (j - p.length)).sum := by omega
      rcases hs (p.length - i) (by omega) (j - p.length) (by omega) he' with hz | hf
      · omega
      · constructor <;> omega
    · rw [second_prefix p n (by omega), second_prefix p n (by omega)] at he
      have hh := prefix_lt n hn (i := i - p.length) (j := j - p.length)
        (by omega) (by omega)
      omega

/-- Kravitz's integer construction, including its two-sided proper-interval conclusion.
The whole word is allowed to have zero sum. -/
theorem exists_integer_strong_ordering (A : Finset ℤ) (hA : 0 ∉ A) :
    ∃ w : List ℤ, w.Perm A.toList ∧
      ∀ i j : ℕ, i < j → j ≤ w.length → (i ≠ 0 ∨ j ≠ w.length) →
        ((w.drop i).take (j - i)).sum ≠ 0 := by
  classical
  let P := A.filter (0 < ·)
  let M := A.filter (· < 0)
  let N := M.image (-·)
  have hP : ∀ x ∈ P, 0 < x := by simp [P]
  have hN : ∀ x ∈ N, 0 < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have : y < 0 := (Finset.mem_filter.mp hy).2
    omega
  obtain ⟨p, n, hpp, hnn, hsep⟩ := separated_positive P N hP hN
  have hp : ∀ x ∈ p, 0 < x := by
    intro x hx
    exact hP x (Finset.mem_toList.mp (hpp.mem_iff.mp hx))
  have hn : ∀ x ∈ n, 0 < x := by
    intro x hx
    exact hN x (Finset.mem_toList.mp (hnn.mem_iff.mp hx))
  let w := p.reverse ++ n.map (-·)
  have hw : w.Perm A.toList := by
    have hpd : p.Nodup := hpp.nodup_iff.mpr P.nodup_toList
    have hnd : n.Nodup := hnn.nodup_iff.mpr N.nodup_toList
    apply (List.perm_ext_iff_of_nodup ?_ A.nodup_toList).2
    · intro x
      simp only [w, List.mem_append, List.mem_reverse, List.mem_map, Finset.mem_toList]
      constructor
      · rintro (hx | ⟨y, hy, rfl⟩)
        · exact (Finset.mem_filter.mp (Finset.mem_toList.mp (hpp.mem_iff.mp hx))).1
        · have hyN := Finset.mem_toList.mp (hnn.mem_iff.mp hy)
          obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hyN
          have hzA : z ∈ A := (Finset.mem_filter.mp hz).1
          simpa [← hzy] using hzA
      · intro hx
        have hx0 : x ≠ 0 := fun he => hA (he ▸ hx)
        by_cases hxpos : 0 < x
        · exact Or.inl (hpp.mem_iff.mpr (Finset.mem_toList.mpr
            (Finset.mem_filter.mpr ⟨hx, hxpos⟩)))
        · right
          refine ⟨-x, hnn.mem_iff.mpr (Finset.mem_toList.mpr ?_), by simp⟩
          exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, by omega⟩, rfl⟩
    · rw [List.nodup_append]
      refine ⟨(List.nodup_reverse.mpr hpd), hnd.map (neg_injective), ?_⟩
      intro x hx y hy hxy
      have hxp := hp x (List.mem_reverse.mp hx)
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have hzp := hn z hz
      omega
  refine ⟨w, hw, ?_⟩
  intro i j hij hj hproper hz
  have hsplit := List.sum_take_add_sum_drop (w.take j) i
  rw [List.take_take, Nat.min_eq_left (by omega : i ≤ j), List.drop_take, hz,
    add_zero] at hsplit
  have hend := collision_endpoints p n hp hn hsep hij hj hsplit
  exact hproper.elim (fun h => h hend.1) (fun h => h hend.2)

end D5.S1.Words.Sequenceability.IntegerStrongOrdering
