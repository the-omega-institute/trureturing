/- GID: D5/S3/Combinatorics/ArcherCyclicPadovan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovan
   mirror-E: none(waiver:padovan-count-for-cyclic-pattern-avoiders)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The cyclic 4132 and circular 1324 avoiders have Padovan cardinality. -/

import D5.S3.Combinatorics.ArcherCyclicPadovanCount
import D5.S3.Combinatorics.ArcherCyclicPadovanArithmetic
import D5.S3.Combinatorics.ArcherCyclicPadovanCycleWords
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovan

open ArcherCyclicDefs ArcherCyclicPadovanClasses
open ArcherCyclicPadovanBijections ArcherCyclicPadovanCount
open ArcherCyclicPadovanRecurrenceUniqueness
open ArcherCyclicPadovanCycleWords ArcherCyclicTetranacciCycleWords

theorem result : ArcherCyclicDefs.padovanClaim := by
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
  let b (n : ℕ) := (goodWords n).ncard
  let d (n : ℕ) := (auxWords n).ncard
  let s (n : ℕ) := ∑ k ∈ Finset.Icc 1 n, d k
  have hshort (ν w : List ℕ) (hν : ν.length = 4) (hw : w.length < 4) :
      ¬ ArrowWilfDefs.Contains ν [] ν.length w := by
    intro h
    obtain ⟨x, _, _, hsub, _⟩ := h
    have hlen := List.Sublist.length_le hsub
    simp only [List.length_map, hν] at hlen
    omega
  have hb₁ : b 1 = 1 := by
    have heq : goodWords 1 = {[1]} := by
      ext w
      constructor
      · intro hw
        have hperm : w.Perm [1] := by simpa [goodWords, circleWords] using hw.1.1
        have hword := List.perm_singleton.mp hperm
        simpa using hword
      · intro hw
        have hword : w = [1] := by simpa using hw
        subst w
        simp only [goodWords, circleWords, Set.mem_ofPred_eq]
        refine ⟨⟨by simp, by rfl, ?_⟩, ?_⟩
        · intro r hr
          exact hshort _ _ (by rfl) (by simp)
        · exact hshort _ _ (by rfl) (by simp [oneLine])
    simp [b, heq]
  have hd₁ : d 1 = 1 := by
    have heq : auxWords 1 = {[1, 2]} := by
      ext w
      constructor
      · intro hw
        have hp : w.Perm [1, 2] := by
          simpa [List.range'] using hw.1.1
        have hh : w.head? = some 1 := hw.1.2.1
        rcases w with _ | ⟨a, t⟩
        · simp at hh
        have ha : a = 1 := by simpa using hh
        subst a
        have ht : t.Perm [2] := List.Perm.cons_inv hp
        have heq : t = [2] := List.perm_singleton.mp ht
        subst t
        simp
      · intro hw
        have hword : w = [1, 2] := by simpa using hw
        subst w
        simp only [auxWords, circleWords, Set.mem_ofPred_eq]
        refine ⟨⟨by decide, by rfl, ?_⟩, ?_⟩
        · intro r hr
          exact hshort _ _ (by rfl) (by simp)
        · unfold tailCondition
          constructor
          · exact hshort _ _ (by rfl) (by simp [oneLine])
          · intro h
            obtain ⟨c, e, hsub, _, _⟩ := h
            have hlen := List.Sublist.length_le hsub
            simp [oneLine] at hlen
    simp [d, heq]
  have hs₀ : s 0 = 0 := by simp [s]
  have hs : ∀ n, s (n + 1) = s n + d (n + 1) := by
    intro n
    simp only [s]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have hb : ∀ n, b (n + 2) = b (n + 1) + s n := by
    intro n
    have h := main_card_recurrence (n + 2) (by omega)
    simpa only [b, s, show n + 2 - 1 = n + 1 by omega,
      show n + 2 - 2 = n by omega, d] using h
  have hd : ∀ n, 1 ≤ n → d (n + 1) = b (n + 1) + d n := by
    intro n hn
    have h := auxiliary_card_recurrence (n + 1) (by omega)
    simpa only [b, d, show n + 1 - 1 = n by omega] using h
  have hrec : (b 2 = 1 ∧ b 3 = 2) ∧
      ∀ n, 1 ≤ n →
        b (n + 3) + 2 * b (n + 1) = 3 * b (n + 2) + b n := by
    have hb₂ : b 2 = 1 := by
      have h := hb 0
      norm_num at h
      omega
    have hs₁ : s 1 = 1 := by
      have h := hs 0
      norm_num at h
      omega
    have hb₃ : b 3 = 2 := by
      have h := hb 1
      norm_num at h
      omega
    refine ⟨⟨hb₂, hb₃⟩, ?_⟩
    intro j hj
    by_cases h1 : j = 1
    · subst j
      have hd₂ := hd 1 (by omega)
      have hs₂ := hs 1
      have hb₄ := hb 2
      simp only [Nat.reduceAdd] at hd₂ hs₂ hb₄ ⊢
      omega
    · have hj2 : 2 ≤ j := by omega
      have hbprev := hb (j - 1)
      have hbnow := hb j
      have hbnext := hb (j + 1)
      have hsprev := hs (j - 1)
      have hsnow := hs j
      have hdnow := hd j hj
      have hjprev : j - 1 + 1 = j := by omega
      have hjprev2 : j - 1 + 2 = j + 1 := by omega
      simp only [hjprev, hjprev2, Nat.add_assoc, Nat.reduceAdd] at *
      omega
  have hb₂ : b 2 = padovan 6 := by
    have h := hrec.1.1
    norm_num [padovan] at ⊢
    exact h
  have hb₃ : b 3 = padovan 9 := by
    have h := hrec.1.2
    norm_num [padovan] at ⊢
    exact h
  have hb₁' : b 1 = padovan 3 := by
    norm_num [padovan]
    exact hb₁
  have hcount := triple_recurrence_unique b hb₁' hb₂ hb₃ hrec.2
  intro n hn
  have hImage : cyclicAvoiders n [4, 1, 3, 2] [1, 3, 2, 4] =
      oneLine '' goodWords n := by
    ext p
    constructor
    · intro hp
      have hlen : p.length = n := by simpa using hp.1.length_eq
      have hw : orbitWord p ∈ goodWords n := by
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · simpa [ArcherCyclicDefs.IsCyclic, hlen] using hp.2.1
        · have hpne : p ≠ [] := by
            intro heq
            simp [heq] at hlen
            omega
          unfold orbitWord
          rw [List.range_map_iterate, List.head?_eq_getElem?, hlen]
          simpa using List.getElem?_iterate (image p) 1 n 0 (by omega)
        · simpa [hlen] using hp.2.2.2
        · simpa [oneLine_orbitWord p (by simpa [hlen] using hp.1) hp.2.1]
            using hp.2.2.1
      exact ⟨orbitWord p, hw,
        oneLine_orbitWord p (by simpa [hlen] using hp.1) hp.2.1⟩
    · rintro ⟨w, hw, rfl⟩
      have hlen : w.length = n := by simpa using hw.1.1.length_eq
      have hform : ∃ v, w = 1 :: v := by
        rcases w with _ | ⟨a, v⟩
        · simp at hlen
          omega
        have ha : a = 1 := by simpa using hw.1.2.1
        exact ⟨v, by simp [ha]⟩
      obtain ⟨v, rfl⟩ := hform
      have hsize : 1 + v.length = n := by simpa [Nat.add_comm] using hlen
      have hperm : (1 :: v).Perm (List.range' 1 (1 + v.length)) := by
        rw [hsize]
        exact hw.1.1
      have horbit := orbitWord_oneLine v hperm
      have hlineperm := oneLine_perm (1 :: v) (by simpa [Nat.add_comm] using hperm)
      have hplength : (oneLine (1 :: v)).length = n := by
        simpa [oneLine, Nat.add_comm] using hsize
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hlen] using hlineperm
      · simpa [ArcherCyclicDefs.IsCyclic, hplength, horbit] using hw.1.1
      · exact hw.2
      · simpa [horbit] using hw.1.2.2
  have hinj : Set.InjOn oneLine (goodWords n) := by
    intro w hw v hv heq
    have hshape (u : List ℕ) (hu : u ∈ goodWords n) : ∃ t, u = 1 :: t := by
      have hlen : u.length = n := by simpa using hu.1.1.length_eq
      rcases u with _ | ⟨a, t⟩
      · simp at hlen
        omega
      have ha : a = 1 := by simpa using hu.1.2.1
      exact ⟨t, by simp [ha]⟩
    obtain ⟨tw, hwshape⟩ := hshape w hw
    obtain ⟨tv, hvshape⟩ := hshape v hv
    have hwperm : (1 :: tw).Perm (List.range' 1 (1 + tw.length)) := by
      have hlen : w.length = n := by simpa using hw.1.1.length_eq
      have hsize : 1 + tw.length = n := by simpa [hwshape, Nat.add_comm] using hlen
      rw [hsize]
      simpa [hwshape] using hw.1.1
    have hvperm : (1 :: tv).Perm (List.range' 1 (1 + tv.length)) := by
      have hlen : v.length = n := by simpa using hv.1.1.length_eq
      have hsize : 1 + tv.length = n := by simpa [hvshape, Nat.add_comm] using hlen
      rw [hsize]
      simpa [hvshape] using hv.1.1
    have hworbit : orbitWord (oneLine w) = w := by
      simpa only [hwshape] using orbitWord_oneLine tw hwperm
    have hvorbit : orbitWord (oneLine v) = v := by
      simpa only [hvshape] using orbitWord_oneLine tv hvperm
    calc
      w = orbitWord (oneLine w) := hworbit.symm
      _ = orbitWord (oneLine v) := by rw [heq]
      _ = v := hvorbit
  rw [hImage]
  exact (hinj.ncard_image).trans (hcount n hn)

end D5.S3.Combinatorics.ArcherCyclicPadovan
