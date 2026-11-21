/- GID: D5/S3/Arith/Divisors/ErdosNicolas/RankIndexed
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: none
   digest: Indexed rank-block upper bounds and exact row-interval concatenation. -/

import D5.S3.Arith.Divisors.ErdosNicolas.RankMajorant
import D5.S3.Arith.Divisors.ErdosNicolas.GapMajorant
import Mathlib.Algebra.BigOperators.Intervals

/-! Structural fuel bounds the number of blocks; each successful step consumes positive length. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Indexed rank blocks use the first denominator of each block and never traverse a list tail. -/
def rankIndexRow (Q R t : ℕ) (d : ℕ → ℕ) (i : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, j =>
      if j < t then
        let s := rankSize R (j - i) (t - j)
        ceilDiv (Q * s) (d j - d i) + rankIndexRow Q R t d i fuel (j + s)
      else 0

/-- The complete integer upper bound consists of all rows of increasing index pairs. -/
def rankIndexUpper (Q R t : ℕ) (d : ℕ → ℕ) : ℕ :=
  ((List.range t).map fun i => rankIndexRow Q R t d i t (i + 1)).sum

private theorem index_block_rounding (Q t : ℕ) (d : ℕ → ℕ)
    (hd : ∀ i j, i < j → j < t → d i < d j)
    {i j s : ℕ} (hij : i < j) (hjt : j < t) (hs : j + s ≤ t) :
    (Q : ℚ) * (∑ k ∈ Ico j (j + s), ((d k : ℚ) - d i)⁻¹) ≤
      ceilDiv (Q * s) (d j - d i) := by
  let xs := (Ico j (j + s)).toList.map d
  have hfirst : d i < d j := hd i j hij hjt
  have hmin : ∀ z ∈ xs, d j ≤ z := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    have hk' := mem_Ico.mp (mem_toList.mp hk)
    by_cases he : k = j
    · subst k; exact le_rfl
    · exact (hd j k (by omega) (by omega)).le
  have hb := rank_block_rounding (Q := Q) hfirst hmin
  have hlen : xs.length = s := by simp [xs, Nat.card_Ico]
  rw [hlen] at hb
  have heq : rowInv (d i) xs =
      ∑ k ∈ Ico j (j + s), ((d k : ℚ) - d i)⁻¹ := by
    simp only [rowInv, xs, List.map_map, Function.comp_def, sum_map_toList]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_Ico.mp hk
    rw [Nat.cast_sub (hd i k (by omega) (by omega)).le]
  rwa [heq] at hb

/-- Sufficient fuel covers the entire remaining index interval, including its last short block. -/
private theorem rankIndexRow_sound (Q R t : ℕ) (d : ℕ → ℕ)
    (hd : ∀ i j, i < j → j < t → d i < d j)
    (i fuel j : ℕ) (hij : i < j) (hjt : j ≤ t) (hf : t - j ≤ fuel) :
    (Q : ℚ) * (∑ k ∈ Ico j t, ((d k : ℚ) - d i)⁻¹) ≤
      rankIndexRow Q R t d i fuel j := by
  induction fuel generalizing j with
  | zero =>
    have he : j = t := by omega
    subst j
    simp [rankIndexRow]
  | succ fuel ih =>
    by_cases hlt : j < t
    · let s := rankSize R (j - i) (t - j)
      have hpos : 1 ≤ s := by dsimp [s, rankSize]; omega
      have hle : s ≤ t - j := Nat.min_le_right _ _
      have hnext : j + s ≤ t := by omega
      have hfirst := index_block_rounding Q t d hd hij hlt hnext
      have htail := ih (j + s) (by omega) hnext (by omega)
      have hsplit :
          (∑ k ∈ Ico j (j + s), ((d k : ℚ) - d i)⁻¹) +
            (∑ k ∈ Ico (j + s) t, ((d k : ℚ) - d i)⁻¹) =
          ∑ k ∈ Ico j t, ((d k : ℚ) - d i)⁻¹ :=
        sum_Ico_consecutive (fun k => ((d k : ℚ) - d i)⁻¹) (by omega) hnext
      rw [rankIndexRow, if_pos hlt]
      change (Q : ℚ) * (∑ k ∈ Ico j t, ((d k : ℚ) - d i)⁻¹) ≤
        ((ceilDiv (Q * s) (d j - d i) +
          rankIndexRow Q R t d i fuel (j + s) : ℕ) : ℚ)
      rw [← hsplit, mul_add, Nat.cast_add]
      exact add_le_add hfirst htail
    · have he : j = t := by omega
      subst j
      simp [rankIndexRow]

private theorem sum_range_cast (t : ℕ) (g : ℕ → ℕ) :
    (((List.range t).map g).sum : ℚ) = ∑ i ∈ range t, (g i : ℚ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [List.sum_range_succ, sum_range_succ, Nat.cast_add, ih]

/-- The indexed checker bounds every pair of a strictly increasing finite sequence. -/
theorem rankIndexUpper_sound (Q R t : ℕ) (d : ℕ → ℕ)
    (hd : ∀ i j, i < j → j < t → d i < d j) :
    (Q : ℚ) * indexPairSum t (fun i => (d i : ℚ)) ≤ rankIndexUpper Q R t d := by
  unfold indexPairSum rankIndexUpper
  rw [mul_sum, sum_range_cast]
  apply sum_le_sum
  intro i hi
  exact rankIndexRow_sound Q R t d hd i t (i + 1) (by omega)
    (by have := mem_range.mp hi; omega) (by omega)

/-- A finite row interval can be checked independently of all other row intervals. -/
def rankIndexRange (Q R t : ℕ) (d : ℕ → ℕ) (start count : ℕ) : ℕ :=
  ((List.range' start count).map fun i => rankIndexRow Q R t d i t (i + 1)).sum

/-- Empty row intervals contribute no numerical terms. -/
private theorem rankIndexRange_zero (Q R t : ℕ) (d : ℕ → ℕ) (start : ℕ) :
    rankIndexRange Q R t d start 0 = 0 := by
  simp [rankIndexRange]

/-- Adjacent intervals partition the same original indexed rank sum exactly. -/
private theorem rankIndexRange_add (Q R t : ℕ) (d : ℕ → ℕ) (start m n : ℕ) :
    rankIndexRange Q R t d start (m + n) =
      rankIndexRange Q R t d start m + rankIndexRange Q R t d (start + m) n := by
  unfold rankIndexRange
  rw [← List.range'_append_1, List.map_append, List.sum_append]

/-- Taking all original rows recovers the unchanged indexed upper-bound computation. -/
private theorem rankIndexRange_all (Q R t : ℕ) (d : ℕ → ℕ) :
    rankIndexRange Q R t d 0 t = rankIndexUpper Q R t d := by
  simp only [rankIndexRange, rankIndexUpper, List.range_eq_range']

/-- Only the short list of interval lengths is traversed when combining opaque row results. -/
def rankIndexChunks (Q R t : ℕ) (d : ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | start, m :: ms =>
      rankIndexRange Q R t d start m + rankIndexChunks Q R t d (start + m) ms

/-- Any finite list of adjacent row lengths partitions precisely the same interval. -/
private theorem rankIndexRange_chunks (Q R t : ℕ) (d : ℕ → ℕ) (start : ℕ) (counts : List ℕ) :
    rankIndexRange Q R t d start counts.sum = rankIndexChunks Q R t d start counts := by
  induction counts generalizing start with
  | nil => simp only [List.sum_nil, rankIndexRange_zero, rankIndexChunks]
  | cons m ms ih =>
    simp only [List.sum_cons, rankIndexRange_add, rankIndexChunks, ih]

/-- Checked row intervals of total length `t` recover the original full upper bound. -/
theorem rankIndexUpper_chunks (Q R t : ℕ) (d : ℕ → ℕ) (counts : List ℕ)
    (hcounts : counts.sum = t) :
    rankIndexUpper Q R t d = rankIndexChunks Q R t d 0 counts := by
  have h := rankIndexRange_chunks Q R t d 0 counts
  rw [hcounts] at h
  exact (rankIndexRange_all Q R t d).symm.trans h

#print axioms rankIndexRow_sound
#print axioms rankIndexUpper_sound

#print axioms rankIndexRange_add
#print axioms rankIndexRange_all
#print axioms rankIndexUpper_chunks

end D5.S3.Arith.ErdosNicolas
