/- GID: D5/S3/Arith/Divisors/ErdosNicolas/RankMajorant
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: none
   digest: Sequential rank blocks and integer upper bounds for complete pair sums. -/

import D5.S3.Arith.Divisors.ErdosNicolas.PairChecker
import Mathlib.Data.List.Pairwise

/-! Each rank row traverses a partition of the full tail, including the last short block. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

/-- Rational sum of reciprocal gaps from one point to a later list. -/
def rowInv (x : ℕ) (ds : List ℕ) : ℚ :=
  (ds.map fun y => ((y - x : ℕ) : ℚ)⁻¹).sum

/-- The deterministic block length, truncated at the end of the row. -/
def rankSize (R k len : ℕ) : ℕ := min (max 1 (k / R)) len

/-- The rounded sum for a whole row; list suffixes are consumed in order. -/
def rankRow (Q R x k : ℕ) (ds : List ℕ) : ℕ :=
  match ds with
  | [] => 0
  | y :: ys =>
    let s := rankSize R k (ys.length + 1)
    ceilDiv (Q * s) (y - x) + rankRow Q R x (k + s) ((y :: ys).drop s)
termination_by ds.length
 decreasing_by
  simp only [List.length_drop, List.length_cons]
  unfold rankSize
  have : 1 ≤ min (max 1 (k / R)) (ys.length + 1) := by omega
  omega

/-- All rows, retaining exactly the increasing orientation of every pair. -/
def rankUpper (Q R : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => rankRow Q R x 1 xs + rankUpper Q R xs

private theorem rowInv_append (x : ℕ) (a b : List ℕ) :
    rowInv x (a ++ b) = rowInv x a + rowInv x b := by
  simp [rowInv]

private theorem rowInv_le_const {x y : ℕ} {ds : List ℕ} (hxy : x < y)
    (hy : ∀ z ∈ ds, y ≤ z) :
    rowInv x ds ≤ (ds.length : ℚ) * ((y - x : ℕ) : ℚ)⁻¹ := by
  induction ds with
  | nil => simp [rowInv]
  | cons z zs ih =>
    have hz := hy z (by simp)
    have hgap : y - x ≤ z - x := Nat.sub_le_sub_right hz x
    have hpos : (0 : ℚ) < ((y - x : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_pos_of_lt hxy
    have hb := inv_anti₀ hpos (show ((y - x : ℕ) : ℚ) ≤ (z - x : ℕ) by
      exact_mod_cast hgap)
    have hi := ih (fun a ha => hy a (by simp [ha]))
    simp only [rowInv, List.map_cons, List.sum_cons] at *
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The rounded first denominator bounds every element of a rank block. -/
theorem rank_block_rounding {Q x y : ℕ} {ds : List ℕ} (hxy : x < y)
    (hy : ∀ z ∈ ds, y ≤ z) :
    (Q : ℚ) * rowInv x ds ≤ ceilDiv (Q * ds.length) (y - x) := by
  have hb := rowInv_le_const hxy hy
  have hq : (0 : ℚ) ≤ Q := Nat.cast_nonneg _
  have hr := reciprocal_le_ceil (Q * ds.length) (y - x)
  push_cast at hr
  nlinarith

/-- Coverage and soundness of the recursively chosen rank blocks. -/
private theorem rankRow_sound (Q R x k : ℕ) (ds : List ℕ)
    (hs : ds.Pairwise (· ≤ ·)) (hx : ∀ y ∈ ds, x < y) :
    (Q : ℚ) * rowInv x ds ≤ rankRow Q R x k ds := by
  induction hn : ds.length using Nat.strong_induction_on generalizing k ds with
  | h len ih =>
    cases ds with
    | nil => simp [rowInv, rankRow]
    | cons y ys =>
      let s := rankSize R k (ys.length + 1)
      have hspos : 1 ≤ s := by dsimp [s, rankSize]; omega
      have hsle : s ≤ (y :: ys).length := by
        dsimp [s, rankSize]
        exact Nat.min_le_right _ _
      have hlen : ((y :: ys).drop s).length < len := by
        simp only [List.length_drop, List.length_cons] at *
        omega
      have hprefix : ∀ z ∈ (y :: ys).take s, y ≤ z := by
        intro z hz
        have hz' := List.mem_of_mem_take hz
        rcases List.mem_cons.mp hz' with rfl | hz'
        · exact le_rfl
        · exact (List.pairwise_cons.mp hs).1 z hz'
      have hfirst := rank_block_rounding (Q := Q) (hx y (by simp)) hprefix
      have htake : ((y :: ys).take s).length = s := List.length_take_of_le hsle
      rw [htake] at hfirst
      have htail := ih _ hlen (k + s) ((y :: ys).drop s) (hs.drop)
        (fun z hz => hx z (List.mem_of_mem_drop hz)) rfl
      have hsplit : rowInv x (y :: ys) =
          rowInv x ((y :: ys).take s) + rowInv x ((y :: ys).drop s) := by
        rw [← rowInv_append, List.take_append_drop]
      rw [rankRow]
      change (Q : ℚ) * rowInv x (y :: ys) ≤
        ((ceilDiv (Q * s) (y - x) +
          rankRow Q R x (k + s) ((y :: ys).drop s) : ℕ) : ℚ)
      push_cast
      rw [hsplit, mul_add]
      exact add_le_add hfirst htail

private theorem pairRat_cons_increasing (x : ℕ) (ds : List ℕ)
    (hx : ∀ y ∈ ds, x < y) : pairRat (x :: ds) = rowInv x ds + pairRat ds := by
  simp only [pairRat, List.map_cons, List.sum_cons, lt_self_iff_false, ↓reduceIte,
    zero_add]
  congr 1
  · unfold rowInv
    apply congrArg List.sum
    apply List.map_congr_left
    intro y hy
    simp only [hx y hy, ↓reduceIte]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro y hy
    simp only [Nat.not_lt.mpr (hx y hy).le, ↓reduceIte, zero_add]

/-- The rank checker bounds the full pair sum of every strictly increasing list. -/
theorem rankUpper_sound (Q R : ℕ) (ds : List ℕ) (hs : ds.Pairwise (· < ·)) :
    (Q : ℚ) * pairRat ds ≤ rankUpper Q R ds := by
  induction ds with
  | nil => simp [pairRat, rankUpper]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hs
    have hr := rankRow_sound Q R x 1 xs (hxs.imp fun h => h.le) hx
    have hi := ih hxs
    rw [pairRat_cons_increasing x xs hx, mul_add, rankUpper, Nat.cast_add]
    exact add_le_add hr hi

#print axioms rankRow_sound
#print axioms rankUpper_sound

end D5.S3.Arith.ErdosNicolas
