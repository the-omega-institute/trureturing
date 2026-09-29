/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacciStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacciStructure
   mirror-E: none(waiver:necessary-form-of-cyclic-avoiders)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: One-line avoidance constrains the high and low arcs. -/

import D5.S3.Combinatorics.ArcherCyclicTetranacciPatterns
import D5.S3.Combinatorics.ArcherCyclicTetranacciCycleWords
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacciStructure

open ArcherCyclicDefs ArcherCyclicTetranacciPatterns ArcherCyclicTetranacciCycleWords

/-- If the high arc does not start at its minimum, its predecessor and last
entry create a 4123 occurrence in the successor permutation. -/
theorem first_high_minimum (a m : ℕ) (u : List ℕ)
    (hperm : (a :: u).Perm (List.range' (m + 3) (u.length + 1)))
    (hnd : (1 :: ((a :: u) ++ 2 :: List.range' 3 m)).Nodup)
    (havoid : ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4
      (1 :: ((a :: u) ++ 2 :: List.range' 3 m)))
    (hone : ¬ ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4
      (oneLine (1 :: ((a :: u) ++ 2 :: List.range' 3 m)))) :
    a = m + 3 := by
  let q := m + 3
  let k := m + 2
  let p := a :: u
  let w := 1 :: (p ++ 2 :: List.range' 3 m)
  have hmin (z : ℕ) (hz : z ∈ p) : q ≤ z :=
    List.left_le_of_mem_range' (hperm.mem_iff.mp hz)
  have ha : q ≤ a := hmin a (by simp [p])
  by_contra hneq
  have hqa : q < a := by dsimp [q] at *; omega
  have hqmem : q ∈ p := hperm.mem_iff.mpr (by simp [q])
  have hqu : q ∈ u := by
    rcases List.mem_cons.mp hqmem with h | h
    · exact False.elim (by dsimp [q] at h; omega)
    · exact h
  obtain ⟨b, v, huv, hqb⟩ := List.eq_append_cons_of_mem hqu
  let pre := a :: b
  have hp : p = pre ++ q :: v := by simp [p, pre, huv]
  let r := pre.getLast (by simp [pre])
  let t := p.getLast (by simp [p])
  have hrmem : r ∈ pre := List.getLast_mem (by simp [pre])
  have hrp : r ∈ p := by rw [hp]; simp [hrmem]
  have htp : t ∈ p := List.getLast_mem (by simp [p])
  have hqr : q < r := by
    have hrlo := hmin r hrp
    have hqrne : q ≠ r := by
      have hpd : p.Nodup := hnd.of_cons.of_append_left
      rw [hp] at hpd
      intro heq
      exact (List.nodup_append'.mp hpd).2.2 hrmem (by simp [heq])
    omega
  have hrt : t < r := by
    by_cases hv : v = []
    · have htq : t = q := by simp [t, hp, hv]
      omega
    · have htv : t ∈ v := by
        have htlast : t = v.getLast hv := by simp [t, hp, hv]
        rw [htlast]
        exact List.getLast_mem hv
      have hrtne : r ≠ t := by
        have hpd : p.Nodup := hnd.of_cons.of_append_left
        rw [hp] at hpd
        intro heq
        exact (List.nodup_append'.mp hpd).2.2 hrmem (by simp [heq, htv])
      have hnrt : ¬ r < t := by
        intro hrt
        have hsub : [r, q, t].Sublist p := by
          rw [hp]
          simpa using (List.singleton_sublist.mpr hrmem).append
            ((List.singleton_sublist.mpr htv).cons_cons q)
        have hsmall (z : ℕ) (hz : z ∈ p ++ 2 :: List.range' 3 m) : 1 < z := by
          rcases List.mem_append.mp hz with hz | hz
          · have hzq := hmin z hz
            dsimp [q] at hzq
            omega
          · rcases List.mem_cons.mp hz with rfl | hz
            · omega
            · have hz3 := List.left_le_of_mem_range' hz
              omega
        exact rooted_suffix_avoids_213 _ hsmall havoid r q t hqr hrt
          (hsub.trans (List.sublist_append_left _ _))
      omega
  have hnext (pre' post : List ℕ) (x y : ℕ)
      (heq : w = pre' ++ x :: y :: post) : w.formPerm x = y := by
    have hrotate : w.rotate pre'.length = x :: y :: (post ++ pre') := by
      rw [heq, List.rotate_append_length_eq]
      simp
    have hd : (x :: y :: (post ++ pre')).Nodup := by
      rw [← hrotate]
      exact List.nodup_rotate.mpr hnd
    rw [← List.formPerm_rotate w hnd pre'.length, hrotate]
    exact List.formPerm_apply_head x y _ hd
  have h1 : w.formPerm 1 = a := by
    exact List.formPerm_apply_head 1 a _ hnd
  have hk : w.formPerm k = 1 := by
    have hlast : w.getLast (by simp [w]) = k := by
      have htail : 2 :: List.range' 3 m = List.range' 2 (m + 1) := by
        simp [List.range'_succ]
      simp [w, htail, k, Nat.add_comm]
    rw [← hlast]
    exact List.formPerm_apply_getLast 1 _
  have hr : w.formPerm r = q := by
    apply hnext (1 :: pre.dropLast) (v ++ 2 :: List.range' 3 m) r q
    dsimp [w]
    rw [hp, ← List.dropLast_append_getLast (l := pre) (by simp [pre])]
    simp [r, List.append_assoc]
  have ht : w.formPerm t = 2 := by
    apply hnext (1 :: p.dropLast) (List.range' 3 m) t 2
    dsimp [w]
    rw [← List.dropLast_append_getLast (l := p) (by simp [p])]
    simp [t, List.append_assoc]
  have htlo := hmin t htp
  have hrlo := hmin r hrp
  have hinrange (z : ℕ) (hz : z ∈ p) : z ∈ List.range' 1 w.length := by
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp (hperm.mem_iff.mp hz)
    simp only [w, p, List.length_cons, List.length_append, List.length_range']
    apply List.mem_range'.mpr
    refine ⟨z - 1, ?_, ?_⟩ <;> dsimp [q] at * <;> omega
  have hkbound : k < w.length + 1 := by simp [w, p, k]; omega
  have hindex : [1, k, t, r].Sublist (List.range' 1 w.length) := by
    have h1k : 1 < k := by dsimp [k]; omega
    have hkt : k < t := by dsimp [k, q] at *; omega
    have hs : [1, k, t, r].Pairwise (· ≤ ·) := by
      simp [List.pairwise_cons]
      omega
    apply List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset (by
        simp
        omega) ?_) hs
      (List.pairwise_le_range' _)
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simp [w, p]
    · apply List.mem_range'.mpr
      exact ⟨k - 1, by omega, by dsimp [k]; omega⟩
    · exact hinrange t htp
    · exact hinrange r hrp
  have hsub : [a, 1, 2, q].Sublist (oneLine w) := by
    simpa [oneLine, h1, hk, ht, hr] using hindex.map w.formPerm
  apply hone
  let x : ℕ → ℕ := fun i =>
    if i = 1 then 1 else if i = 2 then 2 else if i = 3 then q else a
  refine ⟨x, ?_, ?_, ?_, by simp⟩
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp [x, q]
    · simp [x, q]
    · simpa [x, q] using hqa
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    apply hsub.subset
    rcases hcases with rfl | rfl | rfl | rfl <;> simp [x]
  · simpa [x, w, p] using hsub

/-- Three or more entries after two force 4123 at one-line indices 1,2,3,4. -/
theorem low_arc_length_le_two (m : ℕ) (u : List ℕ)
    (hnd : (1 :: (((m + 3) :: u) ++ 2 :: List.range' 3 m)).Nodup)
    (hone : ¬ ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4
      (oneLine (1 :: (((m + 3) :: u) ++ 2 :: List.range' 3 m)))) :
    m ≤ 2 := by
  by_contra hlarge
  obtain ⟨j, hj⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  subst m
  let w := 1 :: (((j + 3 + 3) :: u) ++ 2 :: List.range' 3 (j + 3))
  have heq : w = 1 :: (((j + 6) :: u) ++ 2 :: 3 :: 4 :: 5 :: List.range' 6 j) := by
    simp [w, List.range'_succ, Nat.add_assoc]
  have hnext (pre post : List ℕ) (x y : ℕ)
      (hsplit : w = pre ++ x :: y :: post) : w.formPerm x = y := by
    have hr : w.rotate pre.length = x :: y :: (post ++ pre) := by
      rw [hsplit, List.rotate_append_length_eq]
      simp
    have hd : (x :: y :: (post ++ pre)).Nodup := by
      rw [← hr]
      exact List.nodup_rotate.mpr hnd
    rw [← List.formPerm_rotate w hnd pre.length, hr]
    exact List.formPerm_apply_head x y _ hd
  have h1 : w.formPerm 1 = j + 6 := by
    simpa [w, Nat.add_assoc] using List.formPerm_apply_head 1 (j + 3 + 3) _ hnd
  have h2 : w.formPerm 2 = 3 := by
    apply hnext (1 :: ((j + 6) :: u)) (4 :: 5 :: List.range' 6 j)
    simpa using heq
  have h3 : w.formPerm 3 = 4 := by
    apply hnext ((1 :: ((j + 6) :: u)) ++ [2]) (5 :: List.range' 6 j)
    simpa [List.append_assoc] using heq
  have h4 : w.formPerm 4 = 5 := by
    apply hnext ((1 :: ((j + 6) :: u)) ++ [2, 3]) (List.range' 6 j)
    simpa [List.append_assoc] using heq
  have hlen : 4 ≤ w.length := by simp [w]; omega
  have hidx : [1, 2, 3, 4].Sublist (List.range' 1 w.length) := by
    change (List.range' 1 4).Sublist (List.range' 1 w.length)
    exact List.range'_sublist_right.mpr hlen
  have hsub : [j + 6, 3, 4, 5].Sublist (oneLine w) := by
    simpa [oneLine, h1, h2, h3, h4] using hidx.map w.formPerm
  apply hone
  let x : ℕ → ℕ := fun i =>
    if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 5 else j + 6
  refine ⟨x, ?_, ?_, ?_, by simp⟩
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl <;> simp [x]
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    apply hsub.subset
    rcases hcases with rfl | rfl | rfl | rfl <;> simp [x]
  · simpa [x, w] using hsub

end D5.S3.Combinatorics.ArcherCyclicTetranacciStructure
