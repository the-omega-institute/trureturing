/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuPaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuPaths
   mirror-E: none(waiver:last-edge-path-decomposition)
   anchors: [mathlib/module/Mathlib.Data.List.Induction]
   utility: none
   digest: Last-edge decomposition gives the bounded-path length recurrence. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuExpansion
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs Step

/-- The peak-weight polynomial for arbitrary endpoints in the bounded strip. -/
noncomputable def pathPolynomial (H L : ℕ) (a b : ℤ) : ℤ[X] := by
  classical
  exact ∑ w ∈ pathWords L, if ValidPath H a b w then X ^ peakWeight 0 w else 0

open Classical in
/-- Deleting the last edge detects precisely the newly created final peak. -/
theorem path_last_edge_recurrence (H : ℕ) (hH : 1 ≤ H) (L : ℕ) (a b : ℤ)
    (hb : 0 ≤ b) (hbH : b ≤ H) :
    pathPolynomial H (L + 2) a b =
      if b = H then pathPolynomial H (L + 1) a (b - 1) else
        pathPolynomial H (L + 1) a (if b = 0 then 0 else b - 1) +
          pathPolynomial H (L + 1) a (b + 1) +
          (X ^ (L + 1) - 1) * pathPolynomial H L a b := by
  classical
  have words_mem (m : ℕ) (w : List Step) : w ∈ pathWords m ↔ w.length = m := by
    induction m generalizing w with
    | zero => simp [pathWords]
    | succ m ih =>
        cases w with
        | nil => simp [pathWords]
        | cons s w => cases s <;> simp [pathWords, ih]
  have snoc_up (w : List Step) (c d : ℤ) :
      ValidPath H c d (w ++ [up]) ↔
        0 < d ∧ d ≤ H ∧ ValidPath H c (d - 1) w := by
    induction w generalizing c with
    | nil => simp only [List.nil_append, ValidPath]; omega
    | cons s w ih => cases s <;> simp only [List.cons_append, ValidPath, ih] <;> tauto
  have snoc_down (w : List Step) (c d : ℤ) :
      ValidPath H c d (w ++ [down]) ↔
        0 ≤ d ∧ d < H ∧ ValidPath H c (d + 1) w := by
    induction w generalizing c with
    | nil => simp only [List.nil_append, ValidPath]; omega
    | cons s w ih => cases s <;> simp only [List.cons_append, ValidPath, ih] <;> tauto
  have snoc_flat (w : List Step) (c d : ℤ) :
      ValidPath H c d (w ++ [flat]) ↔ d = 0 ∧ ValidPath H c 0 w := by
    induction w generalizing c with
    | nil => simp only [List.nil_append, ValidPath]; omega
    | cons s w ih => cases s <;> simp only [List.cons_append, ValidPath, ih] <;> tauto
  have weight (w : List Step) (offset : ℕ) (s : Step) :
      peakWeight offset (w ++ [s]) = peakWeight offset w +
        if s = down ∧ w.getLast? = some up then offset + w.length else 0 := by
    induction w using List.twoStepInduction generalizing offset with
    | nil => cases s <;> simp [peakWeight]
    | singleton x => cases x <;> cases s <;> simp [peakWeight]
    | cons_cons x y w ih ih' =>
        cases x <;> cases y
        case up.down =>
          rw [List.cons_append, List.cons_append, peakWeight, peakWeight, ih (offset + 2)]
          cases w with
          | nil => cases s <;> simp [peakWeight]
          | cons z w =>
              simp only [List.getLast?_cons_cons, List.length_cons]
              split_ifs <;> omega
        all_goals
          first
          | simpa only [List.cons_append, peakWeight, List.getLast?_cons_cons,
              List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using ih' up (offset + 1)
          | simpa only [List.cons_append, peakWeight, List.getLast?_cons_cons,
              List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using ih' down (offset + 1)
          | simpa only [List.cons_append, peakWeight, List.getLast?_cons_cons,
              List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using ih' flat (offset + 1)
  have split_last (m : ℕ) (f : List Step → ℤ[X]) :
      (∑ w ∈ pathWords (m + 1), f w) =
        (∑ w ∈ pathWords m, f (w ++ [up])) +
        (∑ w ∈ pathWords m, f (w ++ [down])) +
        (∑ w ∈ pathWords m, f (w ++ [flat])) := by
    let S : Finset Step := {up, down, flat}
    have he :
        (∑ p ∈ S.product (pathWords m), f (p.2 ++ [p.1])) =
          ∑ w ∈ pathWords (m + 1), f w := by
      apply Finset.sum_bij (fun p _ => p.2 ++ [p.1])
      · intro p hp
        rw [words_mem, List.length_append, List.length_singleton,
          (words_mem m p.2).mp (Finset.mem_product.mp hp).2]
      · intro p hp q hq heq
        have hp' := (words_mem m p.2).mp (Finset.mem_product.mp hp).2
        have hq' := (words_mem m q.2).mp (Finset.mem_product.mp hq).2
        have h := List.append_inj heq (by omega)
        apply Prod.ext
        · simpa using h.2
        · exact h.1
      · intro w hw
        have hw' := (words_mem (m + 1) w).mp hw
        cases w using List.reverseRecOn with
        | nil => simp at hw'
        | append_singleton w s =>
            refine ⟨(s, w), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
            · cases s <;> simp [S]
            · apply (words_mem m w).mpr
              simpa using hw'
      · intro p hp
        rfl
    rw [← he, Finset.product_eq_sprod, Finset.sum_product]
    simp [S, add_assoc]
  let U (m : ℕ) (d : ℤ) : ℤ[X] :=
    ∑ w ∈ pathWords m,
      if ValidPath H a d w ∧ w.getLast? = some up then X ^ peakWeight 0 w else 0
  have up_arrival (m : ℕ) (d : ℤ) :
      U (m + 1) d = if 0 < d ∧ d ≤ H then pathPolynomial H m a (d - 1) else 0 := by
    dsimp only [U]
    rw [split_last]
    simp only [List.getLast?_append_cons, List.getLast?_singleton, Option.some.injEq,
      reduceCtorEq, and_false, and_true, ite_false, Finset.sum_const_zero, add_zero]
    by_cases hd : 0 < d ∧ d ≤ H
    · simp only [hd, ite_true]
      unfold pathPolynomial
      apply Finset.sum_congr rfl
      intro w hw
      rw [snoc_up, weight]
      simp [hd.1, hd.2]
    · simp only [hd, ite_false]
      apply Finset.sum_eq_zero
      intro w hw
      rw [snoc_up]
      simp only [← and_assoc, hd, false_and, ite_false]
  have one_step (m : ℕ) (d : ℤ) (hd : 0 ≤ d) (hdH : d ≤ H) :
      pathPolynomial H (m + 1) a d =
        (if 0 < d then pathPolynomial H m a (d - 1) else 0) +
        (if d < H then pathPolynomial H m a (d + 1) +
          (X ^ m - 1) * U m (d + 1) else 0) +
        (if d = 0 then pathPolynomial H m a 0 else 0) := by
    unfold pathPolynomial
    rw [split_last]
    congr 1
    · congr 1
      · by_cases h : 0 < d
        · simp only [h, ite_true]
          apply Finset.sum_congr rfl
          intro w hw
          rw [snoc_up, weight]
          simp [h, hdH]
        · simp only [h, ite_false]
          apply Finset.sum_eq_zero
          intro w hw
          simp [snoc_up, h]
      · by_cases h : d < H
        · simp only [h, ite_true]
          dsimp only [U]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w hw
          rw [snoc_down, weight, (words_mem m w).mp hw]
          by_cases hv : ValidPath H a (d + 1) w <;>
            by_cases hu : w.getLast? = some up <;>
            simp [hd, h, hv, hu, pow_add] <;> ring
        · simp only [h, ite_false]
          apply Finset.sum_eq_zero
          intro w hw
          simp [snoc_down, h]
    · by_cases h : d = 0
      · simp only [h, ite_true]
        apply Finset.sum_congr rfl
        intro w hw
        rw [snoc_flat, weight]
        simp [h]
      · simp only [h, ite_false]
        apply Finset.sum_eq_zero
        intro w hw
        simp [snoc_flat, h]
  rw [show L + 2 = (L + 1) + 1 by omega, one_step (L + 1) b hb hbH]
  by_cases htop : b = H
  · have hpos : 0 < b := by omega
    have hn0 : b ≠ 0 := by omega
    simp only [if_pos hpos, if_neg (show ¬ b < H by omega), if_neg hn0,
      if_pos htop, add_zero]
  · have hlt : b < H := by omega
    rw [if_neg htop, if_pos hlt, up_arrival]
    have hu : 0 < b + 1 ∧ b + 1 ≤ H := by omega
    rw [if_pos hu]
    have hback : b + 1 - 1 = b := by omega
    rw [hback]
    by_cases hz : b = 0
    · simp [hz]
      ring
    · have hpos : 0 < b := by omega
      simp [hz, hpos, add_assoc]

end D5.S3.Combinatorics.CylindricPartition.LiUncu
