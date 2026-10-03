/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanCount
   mirror-E: none(waiver:finite-branch-count-for-cyclic-padovan-proof)
   anchors: [mathlib/module/Mathlib.Data.Set.Card.Arithmetic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Disjoint high-block images give a cardinal recurrence. -/

import D5.S3.Combinatorics.ArcherCyclicPadovanBijections
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanCount

open ArcherCyclicPadovanClasses ArcherCyclicPadovanBijections
open ArcherCyclicPadovanPatterns ArcherCyclicTetranacciInsertion

theorem main_card_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (goodWords n).ncard = (goodWords (n - 1)).ncard +
      ∑ k ∈ Finset.Icc 1 (n - 2), (auxWords k).ncard := by
  let I := Finset.Icc 1 (n - 2)
  let B (k : ℕ) : Set (List ℕ) := highInsert (n - k) '' auxWords k
  have hfinite (j : ℕ) : (goodWords j).Finite := by
    apply ((List.range' 1 j).permutations.finite_toSet).subset
    intro v hv
    exact List.mem_permutations.mpr hv.1.1
  have hauxfinite (k : ℕ) : (auxWords k).Finite := by
    apply ((List.range' 1 (k + 1)).permutations.finite_toSet).subset
    intro v hv
    exact List.mem_permutations.mpr hv.1.1
  have hBfinite (k : ℕ) : (B k).Finite := (hauxfinite k).image _
  have hBcard (k : ℕ) (hk : k ∈ I) :
      (B k).ncard = (auxWords k).ncard := by
    have hbounds := Finset.mem_Icc.mp hk
    have hm : 2 ≤ n - k := by dsimp [I] at hk; omega
    apply Set.InjOn.ncard_image
    intro u hu v hv heq
    rcases u with _ | ⟨a, s⟩
    · have hh := hu.1.2.1
      simp at hh
    rcases v with _ | ⟨b, t⟩
    · have hh := hv.1.2.1
      simp at hh
    have ha : a = 1 := by simpa using hu.1.2.1
    have hb : b = 1 := by simpa using hv.1.2.1
    subst a
    subst b
    have hmap : s.map (raiseHigh (n - k)) = t.map (raiseHigh (n - k)) := by
      have hh := (List.cons.inj heq).2
      exact List.append_cancel_right hh
    have hmono : StrictMono (raiseHigh (n - k)) := by
      apply strictMono_nat_of_lt_succ
      intro x
      simp only [raiseHigh]
      split_ifs <;> omega
    have hinj := hmono.injective
    have hst := (List.map_injective_iff.mpr hinj) hmap
    simp [hst]
  have hfrontfinite : ((insertWord 1) '' goodWords (n - 1)).Finite :=
    (hfinite (n - 1)).image _
  have hfrontcard : ((insertWord 1) '' goodWords (n - 1)).ncard =
      (goodWords (n - 1)).ncard := by
    apply Set.InjOn.ncard_image
    intro u hu v hv heq
    rcases u with _ | ⟨a, s⟩
    · have hh := hu.1.2.1
      simp at hh
    rcases v with _ | ⟨b, t⟩
    · have hh := hv.1.2.1
      simp at hh
    have ha : a = 1 := by simpa using hu.1.2.1
    have hb : b = 1 := by simpa using hv.1.2.1
    subst a
    subst b
    have hmap : s.map (fun z => 1 + z) = t.map (fun z => 1 + z) := by
      simpa [insertWord, insertWord] using heq
    have hinj : Function.Injective (fun z : ℕ => 1 + z) := by
      intro x y hxy
      change 1 + x = 1 + y at hxy
      omega
    have hst := (List.map_injective_iff.mpr hinj) hmap
    simp [hst]
  have hnoTwo (m x : ℕ) (hm : 2 ≤ m) : raiseHigh m x ≠ 2 := by
    by_cases hx : x < 2
    · simp [raiseHigh, hx]
      omega
    · simp [raiseHigh, hx]
      omega
  have hsecond (k : ℕ) (hk : k ∈ I) (u : List ℕ) (hu : u ∈ auxWords k) :
      (highInsert (n - k) u).tail.head? ≠ some 2 := by
    have hlen : u.length = k + 1 := by simpa using hu.1.1.length_eq
    rcases u with _ | ⟨a, s⟩
    · simp at hlen
    have ha : a = 1 := by simpa using hu.1.2.1
    subst a
    rcases s with _ | ⟨h, T⟩
    · simp at hlen
      have hkpos := (Finset.mem_Icc.mp hk).1
      omega
    have hm : 2 ≤ n - k := by
      have hbounds := Finset.mem_Icc.mp hk
      dsimp [I] at hk
      omega
    simp only [highInsert, List.tail_cons, List.map_cons]
    intro hh
    have heq : raiseHigh (n - k) h = 2 := Option.some.inj hh
    exact hnoTwo (n - k) h hm heq
  have hfrontDisj : Disjoint ((insertWord 1) '' goodWords (n - 1))
      (⋃ k ∈ I, B k) := by
    rw [Set.disjoint_left]
    intro w hwfront hwB
    obtain ⟨v, hv, rfl⟩ := hwfront
    rcases v with _ | ⟨a, s⟩
    · have hh := hv.1.2.1
      simp at hh
    have ha : a = 1 := by simpa using hv.1.2.1
    subst a
    rcases Set.mem_iUnion.mp hwB with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hki, hbranch⟩
    obtain ⟨u, hu, heq⟩ := hbranch
    have hhead := congrArg (fun z : List ℕ => z.tail.head?) heq
    have hfront : (insertWord 1 (1 :: s)).tail.head? = some 2 := by
      simp [insertWord, insertWord]
    rw [hfront] at hhead
    exact (hsecond k hki u hu) hhead
  have hpair : (I : Set ℕ).PairwiseDisjoint B := by
    intro k hk l hl hne
    change Disjoint (B k) (B l)
    rw [Set.disjoint_left]
    intro w hwk hwl
    obtain ⟨u, hu, rfl⟩ := hwk
    obtain ⟨v, hv, heq⟩ := hwl
    have hm : 2 ≤ n - k := by
      have hbounds := Finset.mem_Icc.mp hk
      omega
    have hlm : 2 ≤ n - l := by
      have hbounds := Finset.mem_Icc.mp hl
      omega
    have htail : u.tail.length = v.tail.length := by
      have hnot (r x : ℕ) (hr : 2 ≤ r) : raiseHigh r x ≠ 2 := by
        by_cases hx : x < 2
        · simp [raiseHigh, hx]
          omega
        · simp [raiseHigh, hx]
          omega
      have hnotRange (r : ℕ) : 2 ∉ List.range' 3 r := by
        intro hh
        have hge := List.left_le_of_mem_range' hh
        omega
      have hpre : 2 ∉ (1 :: u.tail.map (raiseHigh (n - k))) := by
        simp only [List.mem_cons, List.mem_map, not_or]
        refine ⟨by omega, ?_⟩
        rintro ⟨x, hx, hxeq⟩
        exact hnot (n - k) x hm hxeq
      have hpost : 2 ∉ List.range' 3 (n - k - 2) := hnotRange _
      have hsplit :
          ((1 :: u.tail.map (raiseHigh (n - k))) ++
            2 :: List.range' 3 (n - k - 2)) =
          ((1 :: v.tail.map (raiseHigh (n - l))) ++
            2 :: List.range' 3 (n - l - 2)) := by
        simpa [highInsert, List.cons_append] using heq.symm
      obtain ⟨hprefix, _, _⟩ :=
        (List.append_cons_inj_of_notMem hpre hpost).mp hsplit
      have hlength := congrArg List.length hprefix
      simpa using hlength
    have huLen : u.length = k + 1 := by simpa using hu.1.1.length_eq
    have hvLen : v.length = l + 1 := by simpa using hv.1.1.length_eq
    have hutail : u.tail.length = k := by
      rcases u with _ | ⟨a, s⟩
      · simp at huLen
      simpa using huLen
    have hvtail : v.tail.length = l := by
      rcases v with _ | ⟨a, s⟩
      · simp at hvLen
      simpa using hvLen
    exact hne (by omega)
  have hbigfinite : (⋃ k ∈ I, B k).Finite := by
    apply (hfinite n).subset
    rw [main_split n hn]
    exact Set.subset_union_right
  have hbigcard : (⋃ k ∈ I, B k).ncard =
      ∑ k ∈ I, (auxWords k).ncard := by
    have hh := (I.finite_toSet).ncard_biUnion
      (by intro k hk; exact hBfinite k) hpair
    have hsum : (⋃ k ∈ I, B k).ncard =
        ∑ k ∈ I, (B k).ncard := by
      rw [finsum_mem_eq_finite_toFinset_sum _ I.finite_toSet] at hh
      simpa using hh
    calc
      _ = ∑ k ∈ I, (B k).ncard := hsum
      _ = ∑ k ∈ I, (auxWords k).ncard := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hBcard k hk
  calc
    (goodWords n).ncard =
        ((insertWord 1) '' goodWords (n - 1) ∪ ⋃ k ∈ I, B k).ncard := by
      rw [main_split n hn]
    _ = ((insertWord 1) '' goodWords (n - 1)).ncard +
        (⋃ k ∈ I, B k).ncard :=
      Set.ncard_union_eq hfrontDisj hfrontfinite hbigfinite
    _ = (goodWords (n - 1)).ncard + ∑ k ∈ I, (auxWords k).ncard := by
      rw [hfrontcard, hbigcard]
    _ = _ := rfl

end D5.S3.Combinatorics.ArcherCyclicPadovanCount
