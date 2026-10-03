/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacciSuccessor
   mirror-E: none(waiver:successor-computation-for-insertion-branches)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Insertion gives a low prefix and relabeled high suffix. -/

import D5.S3.Combinatorics.ArcherCyclicTetranacciInsertion
import D5.S3.Combinatorics.ArcherCyclicTetranacciCycleWords
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacciSuccessor

open ArcherCyclicDefs ArcherCyclicTetranacciInsertion ArcherCyclicTetranacciCycleWords

def relabel (k z : ℕ) : ℕ :=
  if z = 0 then 0 else if z = 1 then (if k = 1 then 1 else 2) else k + z

def lowPrefix (k : ℕ) : List ℕ :=
  if k = 1 then [2] else (k + 1) :: (List.range' 3 (k - 2) ++ [1])

/-- Computing the successors on each arc identifies the one-line insertion
with a low prefix followed by an increasing relabeling of the old permutation. -/
theorem oneLine_insert (k : ℕ) (s : List ℕ) (hk : 1 ≤ k)
    (hv : (1 :: s).Perm (List.range' 1 (s.length + 1))) :
    oneLine (insertWord k (1 :: s)) =
      lowPrefix k ++ (oneLine (1 :: s)).map (relabel k) := by
  let v := 1 :: s
  let p := v.map (fun z => k + z)
  let l := List.range' 2 (k - 1)
  let w := insertWord k v
  have hvnd : v.Nodup := hv.nodup_iff.mpr List.nodup_range'
  have hvpos (z : ℕ) (hz : z ∈ v) : 1 ≤ z :=
    List.left_le_of_mem_range' (hv.mem_iff.mp hz)
  have hppos (z : ℕ) (hz : z ∈ p) : k < z := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    have := hvpos a ha
    omega
  have hlbound (z : ℕ) (hz : z ∈ l) : 2 ≤ z ∧ z ≤ k := by
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hz
    omega
  have hnd : w.Nodup := by
    rw [show w = 1 :: (p ++ l) by rfl, List.nodup_cons, List.nodup_append']
    refine ⟨?_, hvnd.map (by intro a b heq; dsimp at heq; omega),
      List.nodup_range', ?_⟩
    · simp only [List.mem_append]
      rintro (h | h)
      · have := hppos 1 h; omega
      · have := hlbound 1 h; omega
    · intro a ha hb
      have := hppos a ha
      have := hlbound a hb
      omega
  have hwlen : w.length = v.length + k := by simp [w, insertWord]; omega
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
  have h1 : w.formPerm 1 = k + 1 := by
    exact List.formPerm_apply_head 1 (k + 1) _ hnd
  have hlow (j : ℕ) (hj : 2 ≤ j) (hjk : j < k) : w.formPerm j = j + 1 := by
    have hlsplit : l = List.range' 2 (j - 2) ++
        j :: (j + 1) :: List.range' (j + 2) (k - j - 1) := by
      dsimp [l]
      calc
        _ = List.range' 2 ((j - 2) + ((k - j - 1) + 2)) := by congr 1; omega
        _ = List.range' 2 (j - 2) ++
            List.range' (2 + (j - 2)) ((k - j - 1) + 2) :=
          List.range'_append_1.symm
        _ = _ := by
          simp only [List.range'_succ]
          rw [show 2 + (j - 2) = j by omega]
    apply hnext ((1 :: p) ++ List.range' 2 (j - 2))
      (List.range' (j + 2) (k - j - 1)) j (j + 1)
    change 1 :: (p ++ l) = _
    rw [hlsplit]
    simp [List.append_assoc]
  have hlastlow (hk2 : 2 ≤ k) : w.formPerm k = 1 := by
    have hlast : w.getLast (by simp [w, insertWord]) = k := by
      have hlne : l ≠ [] := by simp [l]; omega
      simp [w, insertWord, l, hlne]
      omega
    rw [← hlast]
    exact List.formPerm_apply_getLast 1 _
  have hentry (j : ℕ) (hj : j < v.length) :
      w[j + 1]'(by rw [hwlen]; omega) = k + v[j] := by
    simp only [w, insertWord, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simpa [p] using hj), List.getElem_map]
  have hhigh (x : ℕ) (hx : x ∈ v) :
      w.formPerm (k + x) = relabel k (v.formPerm x) := by
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    rw [← hjx, ← hentry j hj]
    by_cases hjnext : j + 1 < v.length
    · have hnew : j + 1 + 1 < w.length := by rw [hwlen]; omega
      rw [List.formPerm_apply_lt_getElem w hnd (j + 1) hnew,
        hentry (j + 1) hjnext, List.formPerm_apply_lt_getElem v hvnd j hjnext]
      have hvalpos := hvpos v[j + 1] (List.getElem_mem hjnext)
      have hvalne : v[j + 1] ≠ 1 := by
        intro heq
        have hzero : v[0]'(by simp [v]) = 1 := rfl
        have hh := hvnd.getElem_inj_iff.mp (heq.trans hzero.symm)
        omega
      simp [relabel, hvalne, show v[j + 1] ≠ 0 by omega]
    · have hjlast : j + 1 = v.length := by omega
      have hold : v.formPerm v[j] = 1 := by
        simpa [hjlast, v] using List.formPerm_apply_getElem v hvnd j hj
      rw [hold]
      by_cases hk1 : k = 1
      · subst k
        have hlastw : j + 1 + 1 = w.length := by rw [hwlen]; omega
        have hval : w.formPerm w[j + 1] = 1 := by
          simpa [hlastw, w, insertWord] using
            List.formPerm_apply_getElem w hnd (j + 1) (by rw [hwlen]; omega)
        simpa [relabel] using hval
      · have hk2 : 2 ≤ k := by omega
        have hnew : j + 1 + 1 < w.length := by rw [hwlen]; omega
        rw [List.formPerm_apply_lt_getElem w hnd (j + 1) hnew]
        have hlfirst : l[0]'(by simp [l]; omega) = 2 := by
          simp [l, List.range'_succ, show k - 1 = (k - 2) + 1 by omega]
        have hnewentry : w[j + 1 + 1] = 2 := by
          simp only [w, insertWord, List.getElem_cons_succ]
          rw [List.getElem_append_right (by simp; omega)]
          simp [hjlast] at hlfirst ⊢
        rw [hnewentry]
        simp [relabel, hk1]
  have hlowlist : (List.range' 1 k).map w.formPerm = lowPrefix k := by
    by_cases hk1 : k = 1
    · subst k
      simp [lowPrefix, List.range'_succ, h1]
    · have hk2 : 2 ≤ k := by omega
      have hrange : List.range' 1 k =
          1 :: (List.range' 2 (k - 2) ++ [k]) := by
        rw [show k = (k - 1) + 1 by omega, List.range'_succ]
        rw [show k - 1 = (k - 2) + 1 by omega, List.range'_concat]
        simp
        omega
      have hmiddle : (List.range' 2 (k - 2)).map w.formPerm =
          List.range' 3 (k - 2) := by
        conv_rhs => rw [show 3 = 2 + 1 by rfl, List.range'_succ_left]
        apply List.map_congr_left
        intro x hx
        obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
        exact hlow x (by omega) (by omega)
      simp [hrange, List.map_append, h1, hmiddle, hlastlow hk2, lowPrefix, hk1]
  have hhighlist : (List.range' (1 + k) v.length).map w.formPerm =
      ((List.range' 1 v.length).map v.formPerm).map (relabel k) := by
    rw [show 1 + k = k + 1 by omega, ← List.map_add_range' 1 v.length 1,
      List.map_map, List.map_map]
    apply List.map_congr_left
    intro x hx
    apply hhigh
    exact hv.mem_iff.mpr (by simpa [v, Nat.add_comm] using hx)
  change (List.range' 1 w.length).map w.formPerm = _
  rw [hwlen, show v.length + k = k + v.length by omega,
    ← List.range'_append_1, List.map_append, hlowlist, hhighlist]
  rfl

end D5.S3.Combinatorics.ArcherCyclicTetranacciSuccessor
