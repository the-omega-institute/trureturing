/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacci
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacci
   mirror-E: none(waiver:enumeration-of-cyclic-pattern-avoiders)
   anchors: [mathlib/module/Mathlib.Data.List.Permutation, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Four disjoint insertion branches count cyclic avoiders. -/

import D5.S3.Combinatorics.ArcherCyclicTetranacciDecomposition
import D5.S3.Combinatorics.ArcherCyclicPadovanCycleWords
import Mathlib.Data.List.Permutation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacci

open ArcherCyclicDefs ArcherCyclicTetranacciInsertion
open ArcherCyclicTetranacciCycleWords ArcherCyclicTetranacciDecomposition

theorem result : ArcherCyclicDefs.tetranacciClaim := by
  have oneLine_perm (w : List ℕ) (hw : w.Perm (List.range' 1 w.length)) :
      (oneLine w).Perm (List.range' 1 w.length) := by
    have hnd : (oneLine w).Nodup :=
      List.Nodup.map w.formPerm.injective List.nodup_range'
    apply List.perm_of_nodup_nodup_toFinset_eq hnd List.nodup_range'
    apply Finset.ext
    intro x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hw.mem_iff.mp (List.formPerm_mem_iff_mem.mpr (hw.mem_iff.mpr hy))
    · intro hx
      let y := w.formPerm.symm x
      have hyw : y ∈ w := by
        apply List.formPerm_mem_iff_mem.mp
        simpa [y] using (hw.mem_iff.mpr hx)
      refine List.mem_map.mpr ⟨y, hw.mem_iff.mp hyw, ?_⟩
      simp [y]
  classical
  have hfinite (n : ℕ) : (words n).Finite := by
    apply ((List.range' 1 n).permutations.finite_toSet).subset
    intro w hw
    exact List.mem_permutations.mpr hw.1
  have hzero : words 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hp, hhead, hc, ho⟩
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hp.length_eq)
    simp [hw] at hhead
  have hone : words 1 = {[1]} := by
    apply Set.ext
    intro w
    constructor
    · rintro ⟨hp, hhead, hc, ho⟩
      have hlen : w.length = 1 := by simpa using hp.length_eq
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
      have ha : a = 1 := by simpa using hhead
      simp [ha]
    · rintro rfl
      refine ⟨List.Perm.refl _, rfl, ?_, ?_⟩
      · rintro r hr ⟨x, hx, hm, hs, ht⟩
        have hlen := hs.length_le
        simp at hlen
      · rintro ⟨x, hx, hm, hs, ht⟩
        have hlen := hs.length_le
        simp [oneLine, List.range'_succ] at hlen
  let B (n k : ℕ) : Set (List ℕ) := insertWord k '' words (n - k)
  have hBfinite (n k : ℕ) : (B n k).Finite := (hfinite (n - k)).image _
  have hBcard (n k : ℕ) : (B n k).ncard = (words (n - k)).ncard := by
    apply Set.InjOn.ncard_image
    intro v hv u hu heq
    have hh : v.map (fun z => k + z) = u.map (fun z => k + z) := by
      exact List.append_cancel_right (List.cons.inj heq).2
    apply (List.map_injective_iff.mpr (show Function.Injective (fun z : ℕ => k + z) by
      intro a b hab; dsimp at hab; omega)) hh
  have hsecond (k : ℕ) (v : List ℕ) (hv : v.head? = some 1) :
      (insertWord k v).tail.head? = some (k + 1) := by
    rcases v with (_ | ⟨a, s⟩)
    · simp at hv
    · have ha : a = 1 := by simpa using hv
      simp [insertWord, ha]
  have hdisjoint (n j k : ℕ) (hjk : j ≠ k) : Disjoint (B n j) (B n k) := by
    rw [Set.disjoint_left]
    rintro w ⟨v, hv, rfl⟩ ⟨u, hu, heq⟩
    have hh := congrArg (fun w : List ℕ => w.tail.head?) heq
    rw [hsecond k u hu.2.1, hsecond j v hv.2.1] at hh
    have hnum := Option.some.inj hh
    exact hjk (by omega)
  let a (n : ℕ) := (words n).ncard
  have hrec (n : ℕ) (hn : 1 < n) :
      a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) := by
    have hset : words n = ((B n 1 ∪ B n 2) ∪ B n 3) ∪ B n 4 := by
      apply Set.ext
      intro w
      constructor
      · intro hw
        obtain ⟨k, v, hk, hk4, hkn, hv, heq⟩ := (decomposition n hn w).mp hw
        have hb : w ∈ B n k := ⟨v, hv, heq.symm⟩
        have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl
        all_goals simp only [Set.mem_union]; tauto
      · intro hw
        have branch (k : ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4) (hb : w ∈ B n k) :
            w ∈ words n := by
          obtain ⟨v, hv, rfl⟩ := hb
          have hkn : k < n := by
            by_contra hh
            have hz : n - k = 0 := by omega
            simp [hz, hzero] at hv
          exact (decomposition n hn _).mpr ⟨k, v, hk, hk4, hkn, hv, rfl⟩
        rcases hw with ((hw | hw) | hw) | hw
        · exact branch 1 (by omega) (by omega) hw
        · exact branch 2 (by omega) (by omega) hw
        · exact branch 3 (by omega) (by omega) hw
        · exact branch 4 (by omega) (by omega) hw
    have hd12 : Disjoint (B n 1) (B n 2) := hdisjoint n 1 2 (by omega)
    have hd3 : Disjoint (B n 1 ∪ B n 2) (B n 3) :=
      Set.disjoint_union_left.mpr ⟨hdisjoint n 1 3 (by omega), hdisjoint n 2 3 (by omega)⟩
    have hd4 : Disjoint ((B n 1 ∪ B n 2) ∪ B n 3) (B n 4) :=
      Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
        ⟨hdisjoint n 1 4 (by omega), hdisjoint n 2 4 (by omega)⟩,
        hdisjoint n 3 4 (by omega)⟩
    change (words n).ncard = _
    rw [hset, Set.ncard_union_eq hd4
      (((hBfinite n 1).union (hBfinite n 2)).union (hBfinite n 3)) (hBfinite n 4),
      Set.ncard_union_eq hd3 ((hBfinite n 1).union (hBfinite n 2)) (hBfinite n 3),
      Set.ncard_union_eq hd12 (hBfinite n 1) (hBfinite n 2),
      hBcard n 1, hBcard n 2, hBcard n 3, hBcard n 4]
  have hcounts : ∀ n, a n = tetranacci (n + 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with (_ | _ | _ | _ | n)
      · simp [a, hzero, tetranacci]
      · simp [a, hone, tetranacci]
      · rw [hrec 2 (by omega), ih 1 (by omega), ih 0 (by omega)]
        simp [tetranacci]
      · rw [hrec 3 (by omega), ih 2 (by omega), ih 1 (by omega), ih 0 (by omega)]
        simp [tetranacci]
      · rw [hrec (n + 4) (by omega),
          show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
          show n + 4 - 3 = n + 1 by omega, show n + 4 - 4 = n by omega,
          ih (n + 3) (by omega), ih (n + 2) (by omega),
          ih (n + 1) (by omega), ih n (by omega)]
        rfl
  intro n hn
  have htransfer :
      (cyclicAvoiders n [4, 1, 2, 3] [1, 3, 2, 4]).ncard = (words n).ncard := by
    apply Set.ncard_congr (fun p _ => orbitWord p)
    · rintro p ⟨hp, hc, ho, hrot⟩
      have hplen : p.length = n := by simpa using hp.length_eq
      have hpself : p.Perm (List.range' 1 p.length) := by simpa [hplen] using hp
      have hroot : (orbitWord p).head? = some 1 := by
        rcases n with (_ | n)
        · omega
        · simp [orbitWord, hplen, List.range_eq_range', List.range'_succ]
      refine ⟨by simpa [ArcherCyclicDefs.IsCyclic, hplen] using hc, hroot, ?_, ?_⟩
      · intro r hr hh
        exact hrot r (by simpa [orbitWord, hplen] using hr) hh
      · rw [ArcherCyclicPadovanCycleWords.oneLine_orbitWord p hpself hc]
        exact ho
    · intro p q hp hq heq
      have hpself : p.Perm (List.range' 1 p.length) := by
        have hh : p.length = n := by simpa using hp.1.length_eq
        simpa [hh] using hp.1
      have hqself : q.Perm (List.range' 1 q.length) := by
        have hh : q.length = n := by simpa using hq.1.length_eq
        simpa [hh] using hq.1
      rw [← ArcherCyclicPadovanCycleWords.oneLine_orbitWord p hpself hp.2.1,
        ← ArcherCyclicPadovanCycleWords.oneLine_orbitWord q hqself hq.2.1, heq]
    · rintro w ⟨hwperm, hwhead, hc, ho⟩
      rcases w with (_ | ⟨a, s⟩)
      · simp at hwhead
      · have ha : a = 1 := by simpa using hwhead
        subst a
        let p := oneLine (1 :: s)
        have hwlen : (1 :: s).length = n := by simpa using hwperm.length_eq
        have hwself : (1 :: s).Perm (List.range' 1 (s.length + 1)) := by
          simpa [← hwlen, Nat.add_comm] using hwperm
        have hpperm : p.Perm (List.range' 1 n) := by
          simpa [p, hwlen] using oneLine_perm (1 :: s) (by simpa using hwself)
        have hplen : p.length = n := by simp [p, oneLine, hwlen]
        have horb : orbitWord p = 1 :: s :=
          orbitWord_oneLine s (by simpa [Nat.add_comm] using hwself)
        have hpcyc : IsCyclic p := by
          change (orbitWord p).Perm (List.range' 1 p.length)
          rw [horb, hplen]
          exact hwperm
        refine ⟨p, ⟨hpperm, hpcyc, ho, ?_⟩, horb⟩
        intro r hr hh
        exact hc r (by simpa [horb, hwlen] using hr) (by simpa [horb] using hh)
  rw [htransfer]
  exact hcounts n

#print axioms result

end D5.S3.Combinatorics.ArcherCyclicTetranacci
