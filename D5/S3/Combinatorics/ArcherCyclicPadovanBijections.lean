/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanBijections
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanBijections
   mirror-E: none(waiver:branch-bijections-for-cyclic-padovan-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The position of 2 gives disjoint insertion branches for the two counting classes. -/

import D5.S3.Combinatorics.ArcherCyclicPadovanClasses
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanBijections

open ArcherCyclicDefs ArcherCyclicPadovanClasses
open ArcherCyclicPadovanFrontRecovery ArcherCyclicPadovanRecovery
open ArcherCyclicTetranacciInsertion ArcherCyclicPadovanPatterns

def highInsert (m : ℕ) (v : List ℕ) : List ℕ :=
  1 :: (v.tail.map (raiseHigh m) ++ 2 :: List.range' 3 (m - 2))

theorem auxiliary_split (k : ℕ) (hk : 2 ≤ k) :
    auxWords k =
      (insertWord 1) '' goodWords k ∪
        highInsert 2 '' auxWords (k - 1) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    obtain hfront | hlast := auxiliary_word_shape k (by omega) w hw
    · obtain ⟨R, hword⟩ := hfront
      have hlen : w.length = k + 1 := by simpa using hw.1.1.length_eq
      have hp : (1 :: 2 :: R).Perm (List.range' 1 (1 :: 2 :: R).length) := by
        have hself : w.Perm (List.range' 1 w.length) := by rw [hlen]; exact hw.1.1
        simpa [hword] using hself
      have hc : ∀ r < (1 :: 2 :: R).length,
          ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: 2 :: R).rotate r) := by
        have hcircle : ∀ r < w.length,
            ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r) := by
          simpa only [hlen] using hw.1.2.2
        simpa [hword] using hcircle
      obtain ⟨s, hsperm, _, heq⟩ := recover_front_word R hp hc
      have hs : s.length + 1 = k := by
        have hsize := congrArg List.length heq
        simp [insertWord] at hsize
        rw [hword] at hlen
        simp at hlen
        omega
      have haux : insertWord 1 (1 :: s) ∈ auxWords (s.length + 1) := by
        simpa [hs, ← heq, hword] using hw
      have hgood := (front_insert_aux_iff s hsperm).mp haux
      left
      refine ⟨1 :: s, ?_, ?_⟩
      · simpa [hs] using hgood
      · simpa only [← heq] using hword.symm
    · obtain ⟨H, hH, hword⟩ := hlast
      have hlen : w.length = k + 1 := by simpa using hw.1.1.length_eq
      have hp : (1 :: (H ++ [2])).Perm
          (List.range' 1 (1 :: (H ++ [2])).length) := by
        have hself : w.Perm (List.range' 1 w.length) := by rw [hlen]; exact hw.1.1
        simpa [hword] using hself
      have hc : ∀ r < (1 :: (H ++ [2])).length,
          ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: (H ++ [2])).rotate r) := by
        have hcircle : ∀ r < w.length,
            ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r) := by
          simpa only [hlen] using hw.1.2.2
        simpa [hword] using hcircle
      obtain ⟨v, hvne, hvperm, _, heq⟩ :=
        recover_high_word H [] hH (by simpa using hp) (by simpa using hc)
      rcases v with _ | ⟨h, T⟩
      · exact (hvne rfl).elim
      have hinsert : w = highInsert 2 (1 :: h :: T) := by
        simpa [highInsert, hword] using heq
      have hs : T.length + 2 = k := by
        rw [hinsert] at hlen
        simp [highInsert] at hlen
        omega
      have haux :
          (1 :: ((h :: T).map (raiseHigh 2) ++ [2])) ∈
            auxWords (T.length + 2) := by
        simpa [hs, hinsert, highInsert] using hw
      have hsmall := (last_insert_aux_iff h T hvperm).mp haux
      right
      refine ⟨1 :: h :: T, ?_, ?_⟩
      · simpa [show T.length + 1 = k - 1 by omega] using hsmall
      · exact hinsert.symm
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · rcases v with _ | ⟨a, s⟩
      · have hh := hv.1.2.1
        simp at hh
      have ha : a = 1 := by simpa using hv.1.2.1
      subst a
      have hs : s.length + 1 = k := by
        have hlen := hv.1.1.length_eq
        simp only [List.length_cons, List.length_range'] at hlen
        omega
      have hp : (1 :: s).Perm (List.range' 1 (1 :: s).length) := by
        simpa [hs, Nat.add_comm] using hv.1.1
      have hnew := (front_insert_aux_iff s hp).mpr (by simpa [hs] using hv)
      simpa [insertWord, hs] using hnew
    · have hlen : v.length = k := by
        have hh := hv.1.1.length_eq
        simp only [List.length_range'] at hh
        omega
      rcases v with _ | ⟨a, s⟩
      · simp at hlen
        omega
      have ha : a = 1 := by simpa using hv.1.2.1
      subst a
      rcases s with _ | ⟨h, T⟩
      · simp at hlen
        omega
      have hs : T.length + 2 = k := by simp at hlen; omega
      have hp : (1 :: h :: T).Perm
          (List.range' 1 (1 :: h :: T).length) := by
        have hh := hv.1.1
        rw [show k - 1 + 1 = k by omega] at hh
        simpa [show (1 :: h :: T).length = k by omega] using hh
      have hsmall : (1 :: h :: T) ∈ auxWords (T.length + 1) := by
        simpa [show T.length + 1 = k - 1 by omega] using hv
      have hnew := (last_insert_aux_iff h T hp).mpr hsmall
      simpa [highInsert, hs] using hnew

theorem auxiliary_card_recurrence (k : ℕ) (hk : 2 ≤ k) :
    (auxWords k).ncard = (goodWords k).ncard + (auxWords (k - 1)).ncard := by
  have hmono : StrictMono (raiseHigh 2) := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [raiseHigh]
    split_ifs <;> omega
  have hgoodfinite : (goodWords k).Finite := by
    apply ((List.range' 1 k).permutations.finite_toSet).subset
    intro v hv
    exact List.mem_permutations.mpr hv.1.1
  have hauxfinite : (auxWords (k - 1)).Finite := by
    apply ((List.range' 1 (k - 1 + 1)).permutations.finite_toSet).subset
    intro v hv
    exact List.mem_permutations.mpr hv.1.1
  have hfrontinj : Set.InjOn (insertWord 1) (goodWords k) := by
    intro v hv u hu heq
    rcases v with _ | ⟨a, s⟩
    · have hh := hv.1.2.1
      simp at hh
    rcases u with _ | ⟨b, t⟩
    · have hh := hu.1.2.1
      simp at hh
    have ha : a = 1 := by simpa using hv.1.2.1
    have hb : b = 1 := by simpa using hu.1.2.1
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
  have hlastinj : Set.InjOn (highInsert 2) (auxWords (k - 1)) := by
    have hshape (v : List ℕ) (hv : v ∈ auxWords (k - 1)) :
        ∃ h T, v = 1 :: h :: T := by
      have hlen : v.length = k := by
        have hh := hv.1.1.length_eq
        simp only [List.length_range'] at hh
        omega
      rcases v with _ | ⟨a, s⟩
      · simp at hlen
        omega
      have ha : a = 1 := by simpa using hv.1.2.1
      subst a
      rcases s with _ | ⟨h, T⟩
      · simp at hlen
        omega
      exact ⟨h, T, rfl⟩
    intro v hv u hu heq
    obtain ⟨h, T, rfl⟩ := hshape v hv
    obtain ⟨g, U, rfl⟩ := hshape u hu
    have hmap : (h :: T).map (raiseHigh 2) = (g :: U).map (raiseHigh 2) := by
      have hh := (List.cons.inj heq).2
      exact List.append_cancel_right hh
    have hinj := (hmono).injective
    have htu := (List.map_injective_iff.mpr hinj) hmap
    simp [htu]
  have hdisj : Disjoint ((insertWord 1) '' goodWords k)
      (highInsert 2 '' auxWords (k - 1)) := by
    rw [Set.disjoint_left]
    rintro w ⟨v, hv, rfl⟩ ⟨u, hu, heq⟩
    rcases v with _ | ⟨a, s⟩
    · have hh := hv.1.2.1
      simp at hh
    have ha : a = 1 := by simpa using hv.1.2.1
    subst a
    have huLen : u.length = k := by
      have hh := hu.1.1.length_eq
      simp only [List.length_range'] at hh
      omega
    rcases u with _ | ⟨b, t⟩
    · simp at huLen
      omega
    have hb : b = 1 := by simpa using hu.1.2.1
    subst b
    rcases t with _ | ⟨g, U⟩
    · simp at huLen
      omega
    have hsecond := congrArg (fun z : List ℕ => z.tail.head?) heq
    have h2 : 2 = raiseHigh 2 g := by
      simpa [insertWord, insertWord, highInsert] using hsecond.symm
    by_cases hg : g < 2
    · simp [raiseHigh, hg] at h2
      omega
    · simp [raiseHigh, hg] at h2
      omega
  rw [auxiliary_split k hk,
    Set.ncard_union_eq hdisj (hgoodfinite.image _) (hauxfinite.image _),
    hfrontinj.ncard_image, hlastinj.ncard_image]

theorem main_split (n : ℕ) (hn : 2 ≤ n) :
    goodWords n =
      (insertWord 1) '' goodWords (n - 1) ∪
        ⋃ k ∈ (Finset.Icc 1 (n - 2)),
          highInsert (n - k) '' auxWords k := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    have hlen : w.length = n := by simpa using hw.1.1.length_eq
    rcases w with _ | ⟨a, s⟩
    · simp at hlen
      omega
    have ha : a = 1 := by simpa using hw.1.2.1
    subst a
    have h2range : 2 ∈ List.range' 1 n :=
      List.mem_range'.mpr ⟨1, by omega, by simp⟩
    have h2w : 2 ∈ 1 :: s := hw.1.1.mem_iff.mpr h2range
    have h2s : 2 ∈ s := by simpa using h2w
    obtain ⟨L, R, hsplit⟩ := List.mem_iff_append.mp h2s
    by_cases hL : L = []
    · subst L
      have hp : (1 :: 2 :: R).Perm (List.range' 1 (1 :: 2 :: R).length) := by
        have hself : (1 :: s).Perm (List.range' 1 (1 :: s).length) := by
          rw [hlen]
          exact hw.1.1
        simpa [hsplit] using hself
      have hc : ∀ r < (1 :: 2 :: R).length,
          ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: 2 :: R).rotate r) := by
        have hcircle : ∀ r < (1 :: s).length,
            ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: s).rotate r) := by
          simpa only [hlen] using hw.1.2.2
        simpa [hsplit] using hcircle
      obtain ⟨t, htperm, _, hword⟩ := recover_front_word R hp hc
      have ht : t.length + 2 = n := by
        have hslen : (1 :: 2 :: R).length = n := by simpa [hsplit] using hlen
        have hsize := congrArg List.length hword
        simp [insertWord] at hslen hsize
        omega
      have hnew : insertWord 1 (1 :: t) ∈ goodWords (t.length + 2) := by
        simpa [ht, ← hword, hsplit] using hw
      have hold := (front_insert_good_iff t htperm).mp hnew
      left
      refine ⟨1 :: t, ?_, ?_⟩
      · simpa [show t.length + 1 = n - 1 by omega] using hold
      · simpa [insertWord, hsplit] using hword.symm
    · have hp : (1 :: (L ++ 2 :: R)).Perm
          (List.range' 1 (1 :: (L ++ 2 :: R)).length) := by
        have hself : (1 :: s).Perm (List.range' 1 (1 :: s).length) := by
          rw [hlen]
          exact hw.1.1
        simpa [hsplit] using hself
      have hc : ∀ r < (1 :: (L ++ 2 :: R)).length,
          ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4
            ((1 :: (L ++ 2 :: R)).rotate r) := by
        have hcircle : ∀ r < (1 :: s).length,
            ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: s).rotate r) := by
          simpa only [hlen] using hw.1.2.2
        simpa [hsplit] using hcircle
      obtain ⟨v, hvne, hvperm, _, hword⟩ :=
        recover_high_word L R hL hp hc
      rcases v with _ | ⟨h, T⟩
      · exact (hvne rfl).elim
      let k := T.length + 1
      let m := R.length + 2
      have hfull : (1 :: s) = highInsert m (1 :: h :: T) := by
        simpa [highInsert, m, hsplit] using hword
      have hsize : n = k + m := by
        have hwordlen := congrArg List.length hfull
        have hm2 : m - 2 = R.length := by dsimp [m]; omega
        simp [highInsert, hm2] at hwordlen
        simp only [List.length_cons] at hlen
        dsimp [k, m]
        omega
      have hnew : (1 :: ((h :: T).map (raiseHigh m) ++
          2 :: List.range' 3 (m - 2))) ∈ goodWords (T.length + 1 + m) := by
        simpa [hsize, hfull, highInsert, k] using hw
      have hold := (high_insert_good_iff h T m (by dsimp [m]; omega) hvperm).mp hnew
      have hk : k ∈ Finset.Icc 1 (n - 2) := by
        apply Finset.mem_Icc.mpr
        dsimp [k, m] at hsize ⊢
        omega
      right
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, ?_⟩⟩
      refine ⟨1 :: h :: T, ?_, ?_⟩
      · simpa [k] using hold
      · simpa [show n - k = m by omega] using hfull.symm
  · intro hw
    rcases hw with ⟨v, hv, rfl⟩ | hw
    · rcases v with _ | ⟨a, s⟩
      · have hh := hv.1.2.1
        simp at hh
      have ha : a = 1 := by simpa using hv.1.2.1
      subst a
      have hsize : s.length + 1 = n - 1 := by
        have hh := hv.1.1.length_eq
        simp only [List.length_cons, List.length_range'] at hh
        omega
      have hp : (1 :: s).Perm (List.range' 1 (1 :: s).length) := by
        simpa [hsize, Nat.add_comm] using hv.1.1
      have hsmall : (1 :: s) ∈ goodWords (s.length + 1) := by
        simpa [hsize] using hv
      have hnew := (front_insert_good_iff s hp).mpr hsmall
      simpa [insertWord, show s.length + 2 = n by omega] using hnew
    · rcases Set.mem_iUnion.mp hw with ⟨k, hk⟩
      rcases Set.mem_iUnion.mp hk with ⟨hki, hbranch⟩
      obtain ⟨v, hv, rfl⟩ := hbranch
      have hbounds := Finset.mem_Icc.mp hki
      have hlen : v.length = k + 1 := by simpa using hv.1.1.length_eq
      rcases v with _ | ⟨a, s⟩
      · simp at hlen
      have ha : a = 1 := by simpa using hv.1.2.1
      subst a
      rcases s with _ | ⟨h, T⟩
      · simp at hlen
        omega
      have hsize : T.length + 1 = k := by simp at hlen; omega
      have hp : (1 :: h :: T).Perm
          (List.range' 1 (1 :: h :: T).length) := by
        simpa [hsize] using hv.1.1
      have hsmall : (1 :: h :: T) ∈ auxWords (T.length + 1) := by
        simpa [hsize] using hv
      have hm : 2 ≤ n - k := by omega
      have hnew := (high_insert_good_iff h T (n - k) hm hp).mpr hsmall
      simpa [highInsert, hsize, show k + (n - k) = n by omega] using hnew

end D5.S3.Combinatorics.ArcherCyclicPadovanBijections
