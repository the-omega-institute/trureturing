/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenAEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenAEnumeration
   mirror-E: none(waiver:fishburn-a-insertion-partition-enumeration)
   anchors: []
   utility: none
   digest: Splitting zero and positive insertion cuts proves the A enumeration at every size. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenACount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenAEnumeration

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic2143 FishburnBasicPatterns FishburnBasicParents
open FishburnTenTenAMonotone FishburnTenTenACount

set_option maxHeartbeats 1600000 in
theorem a_enumeration (size : ℕ) :
    (avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]).ncard =
      if size = 0 then 1 else size + 2 * size.choose 3 := by
  classical
  let family := fun n => avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]
  have hfinite (n : ℕ) : (family n).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  letI (n : ℕ) : Finite (family n) := (hfinite n).to_subtype
  have hzero (n : ℕ) (p : List ℕ) (hp : p ∈ family n) :
      p.insertIdx 0 (n + 1) ∈ family (n + 1) := by
    have hmax (value : ℕ) (hv : value ∈ p) : value < n + 1 := by
      have hm := hp.1.mem_iff.mp hv
      simp only [List.mem_range'_1] at hm
      omega
    refine ⟨?_, ?_, ?_⟩
    · apply (List.perm_insertIdx (n + 1) p (by omega)).trans
      apply (hp.1.cons (n + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
    · apply (isFishburn_insertIdx_max_iff p (n + 1) 0 (by omega) hmax).mpr
      exact ⟨hp.2.1, by intro before later hb; omega⟩
    · intro pattern hpattern hocc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl
      · rcases (maximum_2143_test n p hp.1 0 (by omega)).mp hocc with
          hh | ⟨_, _, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
      · rcases (maximum_pattern_tests n p hp.1 0 (by omega)).2.2.mp hocc with
          hh | ⟨_, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
      · rcases (maximum_pattern_tests n p hp.1 0 (by omega)).2.1.mp hocc with
          hh | ⟨_, _, _, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
  have hstep (n : ℕ) (hn : 2 ≤ n) :
      (family (n + 1)).ncard = (family n).ncard + (1 + 2 * n.choose 2) := by
    let Positive := {entry : List ℕ × ℕ // entry.1 ∈ family n ∧ 0 < entry.2 ∧
      entry.2 ≤ n ∧ entry.1.insertIdx entry.2 (n + 1) ∈ family (n + 1)}
    let Active := {entry : List ℕ × ℕ // entry.1 ∈ family n ∧
      entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈ family (n + 1)}
    let embed : Positive → family n × Fin (n + 1) := fun entry =>
      (⟨entry.val.1, entry.property.1⟩, ⟨entry.val.2, by have := entry.property; omega⟩)
    have hembed : Function.Injective embed := by
      intro first second heq
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun pair : family n × Fin (n + 1) => pair.1.val) heq
      · exact congrArg (fun pair : family n × Fin (n + 1) => pair.2.val) heq
    letI : Finite Positive := Finite.of_injective embed hembed
    let split : family n ⊕ Positive → Active := fun entry =>
      match entry with
      | .inl parent => ⟨(parent.val, 0), parent.property, by omega,
          hzero n parent.val parent.property⟩
      | .inr entry => ⟨entry.val, entry.property.1, by
          have hlen : entry.val.1.length = n := by simpa using entry.property.1.1.length_eq
          have := entry.property.2.2.1
          omega, entry.property.2.2.2⟩
    have hsplit : Function.Bijective split := by
      constructor
      · intro first second heq
        cases first with
        | inl first =>
          cases second with
          | inl second =>
            congr 1
            apply Subtype.ext
            exact congrArg (fun entry : Active => entry.val.1) heq
          | inr second =>
            have hh := congrArg (fun entry : Active => entry.val.2) heq
            have := second.property.2.1
            change 0 = second.val.2 at hh
            omega
        | inr first =>
          cases second with
          | inl second =>
            have hh := congrArg (fun entry : Active => entry.val.2) heq
            have := first.property.2.1
            change first.val.2 = 0 at hh
            omega
          | inr second =>
            congr 1
            apply Subtype.ext
            exact congrArg (fun entry : Active => entry.val) heq
      · intro entry
        by_cases hz : entry.val.2 = 0
        · refine ⟨.inl ⟨entry.val.1, entry.property.1⟩, ?_⟩
          apply Subtype.ext
          exact Prod.ext rfl hz.symm
        · have hlen : entry.val.1.length = n := by simpa using entry.property.1.1.length_eq
          refine ⟨.inr ⟨entry.val, entry.property.1, by omega,
            by have := entry.property.2.1; omega, entry.property.2.2⟩, rfl⟩
    have hchildren := maximum_insertion_bijection n
      [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]
    have hcard : Nat.card (family (n + 1)) = Nat.card (family n) + Nat.card Positive := by
      rw [← Nat.card_congr (Equiv.ofBijective _ hchildren),
        ← Nat.card_congr (Equiv.ofBijective split hsplit), Nat.card_sum]
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
    congr 1
    exact a_positive_cut_count n hn
  have hsmall (n : ℕ) (hn : n ≤ 1) : family n = {List.range' 1 n} := by
    ext p
    constructor
    · intro hp
      by_cases hz : n = 0
      · subst n
        have heq : p = [] := List.perm_nil.mp hp.1
        simpa using heq
      · have heq : n = 1 := by omega
        subst n
        have hperm : p.Perm [1] := by simpa only [List.range'_one] using hp.1
        simpa only [Set.mem_singleton_iff, List.range'_one] using List.perm_singleton.mp hperm
    · intro hp
      have heq : p = List.range' 1 n := Set.mem_singleton_iff.mp hp
      subst p
      exact (a_monotone_forms n).1
  have htwo : family 2 = {[1, 2], [2, 1]} := by
    ext p
    constructor
    · intro hp
      obtain ⟨entry, heq⟩ := (maximum_insertion_bijection 1
        [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]).2 ⟨p, hp⟩
      have hparent : entry.val.1 = [1] := by
        have hh : entry.val.1 ∈ family 1 := entry.property.1
        rw [hsmall 1 le_rfl] at hh
        simpa only [List.range'_one, Set.mem_singleton_iff] using hh
      have hchild : entry.val.1.insertIdx entry.val.2 2 = p :=
        congrArg Subtype.val heq
      have hs : entry.val.2 ≤ 1 := by
        have := entry.property.2.1
        rw [hparent] at this
        simpa using this
      have hcuts : entry.val.2 = 0 ∨ entry.val.2 = 1 := by omega
      rw [hparent] at hchild
      rcases hcuts with hc | hc
      · rw [hc] at hchild
        simpa only [List.insertIdx_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
          using (Or.inr hchild.symm : p = [1, 2] ∨ p = [2, 1])
      · rw [hc] at hchild
        exact Or.inl hchild.symm
    · intro hp
      rcases hp with hp | hp
      · rw [hp]
        exact (a_monotone_forms 2).1
      · have heq : p = [2, 1] := Set.mem_singleton_iff.mp hp
        rw [heq]
        exact (a_monotone_forms 2).2.1
  change (family size).ncard = _
  induction size with
  | zero => simp only [hsmall 0 (by omega), Set.ncard_singleton, ↓reduceIte]
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      rw [hsmall 1 le_rfl]
      simp [Nat.choose_eq_zero_of_lt (by omega : 1 < 3)]
    by_cases hone : n = 1
    · subst n
      rw [htwo]
      norm_num
    have hn : 2 ≤ n := by omega
    rw [hstep n hn, ih, if_neg hz, if_neg (by omega : n + 1 ≠ 0)]
    have hpascal := Nat.choose_succ_succ n 2
    change (n + 1).choose 3 = n.choose 2 + n.choose 3 at hpascal
    rw [hpascal]
    omega

end D5.S3.Combinatorics.Fishburn.FishburnTenTenAEnumeration
