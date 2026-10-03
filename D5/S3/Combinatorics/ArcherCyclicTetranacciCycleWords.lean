/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacciCycleWords
   mirror-E: none(waiver:rooted-cycle-word-transfer-has-no-independent-empirical-mirror)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.List, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The successor permutation preserves the interval and recovers its rooted cycle word. -/

import D5.S3.Combinatorics.ArcherCyclicDefs
import Mathlib.GroupTheory.Perm.List
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacciCycleWords

open D5.S3.Combinatorics.ArcherCyclicDefs

/-- The one-line notation of the successor permutation of a cycle word. -/
def oneLine (w : List ℕ) : List ℕ :=
  (List.range' 1 w.length).map w.formPerm

/-- For a rooted word containing exactly `[1,n]`, the successor permutation
constructed with `List.formPerm` has precisely that word as its orbit from 1. -/
theorem orbitWord_oneLine (v : List ℕ)
    (hperm : (1 :: v).Perm (List.range' 1 (1 + v.length))) :
    orbitWord (oneLine (1 :: v)) = 1 :: v := by
  let w : List ℕ := 1 :: v
  let p := oneLine w
  have hnd : w.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hlength : p.length = w.length := by simp [p, oneLine]
  have himage (x : ℕ) (hx : x ∈ w) : image p x = w.formPerm x := by
    have hxr : x ∈ List.range' 1 w.length := by
      simpa [w, Nat.add_comm] using hperm.mem_iff.mp hx
    have hxlo : 1 ≤ x := List.left_le_of_mem_range' hxr
    have hxhi : x - 1 < w.length := by
      obtain ⟨j, hj, hjx⟩ := List.mem_range'.mp hxr
      omega
    unfold image
    rw [List.getD_eq_getElem (l := p) 0 (by simpa [hlength] using hxhi)]
    simp only [p, oneLine, List.getElem_map]
    rw [List.getElem_range'_1]
    congr 1
    omega
  have hentry (i : ℕ) (hi : i < w.length) :
      (image p)^[i] 1 = w[i] := by
    induction i with
    | zero => simp [w]
    | succ i ih =>
      have hip : i < w.length := by omega
      have hnext : i + 1 < w.length := by omega
      rw [Function.iterate_succ_apply', ih hip, himage w[i] (List.getElem_mem hip)]
      exact List.formPerm_apply_lt_getElem w hnd i hnext
  apply List.ext_getElem
  · simp [orbitWord, oneLine]
  · intro i hi hi'
    simp only [orbitWord, List.getElem_map, List.getElem_range] at hi ⊢
    exact hentry i hi'

end D5.S3.Combinatorics.ArcherCyclicTetranacciCycleWords
