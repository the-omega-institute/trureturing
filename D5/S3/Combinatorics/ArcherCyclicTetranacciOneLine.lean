/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacciOneLine
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacciOneLine
   mirror-E: none(waiver:one-line-avoidance-under-low-arc-insertion)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The four insertion branches preserve one-line 4123 avoidance. -/

import D5.S3.Combinatorics.ArcherCyclicTetranacciSuccessor
import D5.S3.Combinatorics.ArcherCyclicPadovanPatterns
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacciOneLine

open ArcherCyclicDefs ArcherCyclicTetranacciInsertion ArcherCyclicTetranacciCycleWords
open ArcherCyclicTetranacciSuccessor

/-- Any occurrence starting at a low index would need an increasing triple
among the remaining low entries; the four permitted prefixes have none. -/
theorem contains_4123_insert_iff (k : ℕ) (s : List ℕ)
    (hk : 1 ≤ k) (hk4 : k ≤ 4)
    (hv : (1 :: s).Perm (List.range' 1 (s.length + 1))) :
    ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4 (oneLine (insertWord k (1 :: s))) ↔
      ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4 (oneLine (1 :: s)) := by
  classical
  let q := oneLine (1 :: s)
  let f := relabel k
  let Q := q.map f
  let small := if k = 1 then 1 else 2
  have hf : StrictMono f := by
    intro a b hab
    dsimp [f, relabel]
    split_ifs <;> omega
  have hmap : ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4 Q ↔
      ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4 q :=
    ArcherCyclicPadovanPatterns.contains_map_iff [4, 1, 2, 3] q f hf
  have hqperm : q.Perm (List.range' 1 (s.length + 1)) := by
    have hperm (w : List ℕ) (hw : w.Perm (List.range' 1 w.length)) :
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
    simpa [q] using hperm (1 :: s) (by simpa using hv)
  have hQnd : Q.Nodup :=
    (hqperm.nodup_iff.mpr List.nodup_range').map hf.injective
  have hQlabel (z : ℕ) (hz : z ∈ Q) : z = small ∨ k + 1 < z := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    have hlo := List.left_le_of_mem_range' (hqperm.mem_iff.mp ha)
    by_cases ha1 : a = 1
    · left
      simp [f, relabel, ha1, small]
    · right
      simp [f, relabel, ha1, show a ≠ 0 by omega]
      omega
  have hprefix (z : ℕ) (hz : z ∈ lowPrefix k) : z ≤ k + 1 := by
    interval_cases k <;> simp [lowPrefix] at hz <;> omega
  have hfiltered :
      (Q.filter (fun z => decide (z ≤ k + 1))).Sublist [small] := by
    have hsng (t : List ℕ) (ht : t.Nodup) (hm : ∀ z ∈ t, z = small) :
        t.Sublist [small] := by
      rcases t with (_ | ⟨a, t⟩)
      · exact List.nil_sublist _
      · have ha : a = small := hm a (by simp)
        have hnil : t = [] := by
          by_contra hne
          obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil t hne
          have heq : b = a := (hm b (by simp [hb])).trans ha.symm
          exact ht.notMem (heq ▸ hb)
        subst a
        rw [hnil]
    apply hsng _ (hQnd.filter _)
    intro z hz
    obtain ⟨hzQ, hzle⟩ := List.mem_filter.mp hz
    have hzbound : z ≤ k + 1 := by simpa using hzle
    rcases hQlabel z hzQ with hh | hh
    · exact hh
    · omega
  have hprefixFilter : (lowPrefix k).filter (fun z => decide (z ≤ k + 1)) =
      lowPrefix k := by
    apply List.filter_eq_self.mpr
    intro z hz
    simp [hprefix z hz]
  have hdropFirst (a : ℕ) (t A B : List ℕ)
      (ha : a ∉ A) (hs : (a :: t).Sublist (A ++ B)) : (a :: t).Sublist B := by
    induction A with
    | nil => simpa using hs
    | cons b A ih =>
      rcases List.cons_sublist_cons'.mp hs with htail | ⟨heq, _⟩
      · exact ih (fun hh => ha (List.mem_cons_of_mem _ hh)) htail
      · exact False.elim (ha (by simp [heq]))
  rw [oneLine_insert k s hk hv]
  change ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4 (lowPrefix k ++ Q) ↔ _
  constructor
  · rintro ⟨x, hx, hm, hs, ht⟩
    have h12 : x 1 < x 2 := hx 1 (by omega) (by simp)
    have h23 : x 2 < x 3 := hx 2 (by omega) (by simp)
    have h34 : x 3 < x 4 := hx 3 (by omega) (by simp)
    change [x 4, x 1, x 2, x 3].Sublist (lowPrefix k ++ Q) at hs
    by_cases hhigh : k + 1 < x 4
    · have hnot : x 4 ∉ lowPrefix k := by
        intro hh
        have := hprefix (x 4) hh
        omega
      have hsub := hdropFirst (x 4) [x 1, x 2, x 3] (lowPrefix k) Q hnot hs
      apply hmap.mp
      refine ⟨x, hx, ?_, hsub, by simp⟩
      intro i hi hik
      apply hsub.subset
      have hik' : i ≤ 4 := by simpa using hik
      have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> simp
    · have hsel : [x 4, x 1, x 2, x 3].filter (fun z => decide (z ≤ k + 1)) =
          [x 4, x 1, x 2, x 3] := by
        apply List.filter_eq_self.mpr
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;>
          simp [show x 4 ≤ k + 1 by omega, show x 1 ≤ k + 1 by omega,
            show x 2 ≤ k + 1 by omega, show x 3 ≤ k + 1 by omega]
      have hs' := hs.filter (fun z => decide (z ≤ k + 1))
      rw [hsel, List.filter_append, hprefixFilter] at hs'
      have hfixed : [x 4, x 1, x 2, x 3].Sublist (lowPrefix k ++ [small]) :=
        hs'.trans ((List.Sublist.refl _).append hfiltered)
      dsimp [small] at hfixed
      interval_cases k <;> simp [lowPrefix, List.range'_succ,
        List.cons_sublist_cons'] at hfixed <;> omega
  · intro hh
    obtain ⟨x, hx, hm, hs, ht⟩ := hmap.mpr hh
    refine ⟨x, hx, ?_, hs.trans (List.sublist_append_right _ _), by simp⟩
    intro i hi hik
    exact List.mem_append_right _ (hm i hi hik)

end D5.S3.Combinatorics.ArcherCyclicTetranacciOneLine
