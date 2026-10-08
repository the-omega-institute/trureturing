/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftReduction
   mirror-E: none(waiver:left-word-linear-reduction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Prefix increments telescope to the signed linear reduction of every active word. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftTree
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftReduction

open InversionSeq207LeftTree

def leftCorrection (depth : ℕ) : List Bool → ℕ → ℤ
  | [], _ => 0
  | entry :: suffix, reserve =>
      leftCorrection depth suffix reserve +
        if entry then
          (leftCount depth (List.replicate (suffix.count false + 1) false) reserve false : ℤ) -
            leftCount depth (List.replicate (suffix.count false) false) reserve false
        else 0

theorem left_linear_reduction (depth : ℕ) (word : List Bool) (reserve : ℕ)
    (maximumActive : Bool)
    (hflag : maximumActive = true → ∃ initial : List Bool, word = initial ++ [true]) :
    (leftCount depth word reserve maximumActive : ℤ) =
      leftCount depth (List.replicate (word.count false) false) reserve false +
        leftCorrection depth word reserve +
        if maximumActive then
          (leftCount depth [] (reserve + 1) false : ℤ) -
            leftCount depth [false] reserve false
        else 0 := by
  have hrec (length : ℕ) (letters : List Bool) (capacity : ℕ) :
      (leftCount (length + 1) letters capacity false : ℤ) =
        (∑ index ∈ Finset.range letters.length,
          if letters.getD index false then (leftCount length [] (capacity + 1) false : ℤ)
          else (leftCount length (letters.take index) (capacity + 1) false : ℤ)) +
        ∑ distance ∈ Finset.range capacity,
          (leftCount length (letters ++ List.replicate distance false ++ [true])
            (capacity - distance) true : ℤ) := by
    simp only [leftCount, Nat.cast_sum]
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro index hindex
      have hlow : index < letters.length := Finset.mem_range.mp hindex
      cases hentry : letters[index] <;> simp [leftChild, hlow, hentry]
    · apply Finset.sum_congr rfl
      intro distance _hdistance
      simp [leftChild, Nat.not_lt.mpr (Nat.le_add_right _ _)]
  have hflagDifference (length : ℕ) (initial : List Bool) (capacity : ℕ) :
      (leftCount length (initial ++ [true]) capacity true : ℤ) -
          leftCount length (initial ++ [true]) capacity false =
        (leftCount length [] (capacity + 1) false : ℤ) -
          leftCount length [false] capacity false := by
    have hisos := left_internal_isomorphisms length
    have hsingle :
        (leftCount length [true] capacity true : ℤ) -
            leftCount length [true] capacity false =
          (leftCount length [] (capacity + 1) false : ℤ) -
            leftCount length [false] capacity false := by
      rw [hisos.2 capacity, hisos.1 [] capacity false (by simp)]
    rw [← hsingle]
    cases length with
    | zero => simp [leftCount]
    | succ length =>
        have hsum (letters : List Bool) :
            (leftCount (length + 1) (letters ++ [true]) capacity true : ℤ) -
                leftCount (length + 1) (letters ++ [true]) capacity false =
              (leftCount length [true] (capacity + 1) true : ℤ) -
                leftCount length [] (capacity + 1) false := by
          simp only [leftCount, Nat.cast_sum, ← Finset.sum_sub_distrib]
          rw [Finset.sum_eq_single letters.length]
          · have hget : (letters ++ [true])[letters.length] = true := by simp
            simp [leftChild, hget]
          · intro index _hindex hne
            by_cases hlow : index < (letters ++ [true]).length
            · have hnotLast : ¬ index + 1 = (letters ++ [true]).length := by
                simp only [List.length_append, List.length_cons, List.length_nil] at *
                omega
              have hdec : decide (index + 1 = (letters ++ [true]).length) = false :=
                decide_eq_false hnotLast
              simp only [leftChild, if_pos hlow, hdec, Bool.and_false,
                Bool.false_eq_true, if_false, sub_self]
            · simp only [leftChild, if_neg hlow, sub_self]
          · intro hnotMem
            exact False.elim (hnotMem (by simp; omega))
        rw [hsum initial]
        simpa using (hsum []).symm
  have hprefix : ∀ length : ℕ, ∀ (letters : List Bool) (capacity : ℕ),
      (leftCount length (false :: letters) capacity false : ℤ) -
          leftCount length letters capacity false =
        (leftCount length (List.replicate (letters.count false + 1) false)
          capacity false : ℤ) -
          leftCount length (List.replicate (letters.count false) false) capacity false := by
    intro length
    induction length with
    | zero => intros; simp [leftCount]
    | succ length ih =>
      have hformula (letters : List Bool) (capacity : ℕ) :
          (leftCount (length + 1) (false :: letters) capacity false : ℤ) -
              leftCount (length + 1) letters capacity false =
            (leftCount length (List.replicate (letters.count false) false)
              (capacity + 1) false : ℤ) +
              ∑ distance ∈ Finset.range capacity,
                ((leftCount length (List.replicate (letters.count false + distance + 1) false)
                    (capacity - distance) false : ℤ) -
                  leftCount length (List.replicate (letters.count false + distance) false)
                    (capacity - distance) false) := by
        let basis (index : ℕ) : ℤ :=
          leftCount length (List.replicate index false) (capacity + 1) false
        have hlow (index : ℕ) (hindex : index < letters.length) :
            (if letters.getD index false then (leftCount length [] (capacity + 1) false : ℤ)
              else (leftCount length ((false :: letters).take (index + 1))
                (capacity + 1) false : ℤ)) -
              (if letters.getD index false then
                (leftCount length [] (capacity + 1) false : ℤ)
              else (leftCount length (letters.take index) (capacity + 1) false : ℤ)) =
            basis ((letters.take (index + 1)).count false) -
              basis ((letters.take index).count false) := by
          have htake : letters.take (index + 1) =
              letters.take index ++ [letters[index]] := List.take_succ_eq_append_getElem hindex
          have hget : letters.getD index false = letters[index] := by
            simp [List.getD, hindex]
          rw [hget, htake]
          cases hentry : letters[index] with
          | false =>
              simpa [basis, List.take_succ_cons, List.count_append, hentry] using
                ih (letters.take index) (capacity + 1)
          | true => simp [List.count_append]
        have hlowSum :
            (∑ index ∈ Finset.range letters.length,
              ((if letters.getD index false then
                (leftCount length [] (capacity + 1) false : ℤ)
              else (leftCount length ((false :: letters).take (index + 1))
                (capacity + 1) false : ℤ)) -
              (if letters.getD index false then
                (leftCount length [] (capacity + 1) false : ℤ)
              else (leftCount length (letters.take index) (capacity + 1) false : ℤ)))) =
            basis (letters.count false) - basis 0 := by
          rw [Finset.sum_congr rfl (fun index hindex => hlow index (Finset.mem_range.mp hindex))]
          simpa using Finset.sum_range_sub
            (fun index => basis ((letters.take index).count false)) letters.length
        have hhigh (distance : ℕ) :
            (leftCount length ((false :: letters) ++ List.replicate distance false ++ [true])
                (capacity - distance) true : ℤ) -
              leftCount length (letters ++ List.replicate distance false ++ [true])
                (capacity - distance) true =
            (leftCount length (List.replicate (letters.count false + distance + 1) false)
                (capacity - distance) false : ℤ) -
              leftCount length (List.replicate (letters.count false + distance) false)
                (capacity - distance) false := by
          have hfirst := hflagDifference length
            ((false :: letters) ++ List.replicate distance false) (capacity - distance)
          have hsecond := hflagDifference length
            (letters ++ List.replicate distance false) (capacity - distance)
          have hbase := ih (letters ++ List.replicate distance false ++ [true])
            (capacity - distance)
          simp at hbase
          simp only [List.append_assoc, List.cons_append] at hfirst hsecond hbase ⊢
          omega
        have hhighSum := Finset.sum_congr (s₁ := Finset.range capacity) rfl
          (fun distance _hdistance => hhigh distance)
        rw [Finset.sum_sub_distrib] at hlowSum hhighSum
        rw [hrec, hrec]
        simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
          List.getD_cons_succ, Bool.false_eq_true, reduceIte, List.take_zero]
        change _ = basis (letters.count false) + _
        have hbaseZero : basis 0 = (leftCount length [] (capacity + 1) false : ℤ) := rfl
        omega
      intro letters capacity
      have hfirst := hformula letters capacity
      have hsecond := hformula (List.replicate (letters.count false) false) capacity
      simp only [List.count_replicate_self] at hsecond
      simpa only [List.count_replicate_self, List.replicate_succ] using
        hfirst.trans hsecond.symm
  have hzeroFlag : ∀ letters : List Bool,
      (leftCount depth letters reserve false : ℤ) =
        leftCount depth (List.replicate (letters.count false) false) reserve false +
          leftCorrection depth letters reserve := by
    intro letters
    induction letters with
    | nil => simp [leftCorrection]
    | cons entry suffix ih =>
        have hinc := hprefix depth suffix reserve
        cases entry with
        | false =>
            simp only [List.count_cons_self, leftCorrection, Bool.false_eq_true,
              if_false, add_zero] at ih hinc ⊢
            omega
        | true =>
            have hiso := (left_internal_isomorphisms depth).1 suffix reserve false (by simp)
            simp only [List.count_cons_of_ne (by decide : true ≠ false), leftCorrection,
              ite_true] at ih hinc ⊢
            rw [hiso]
            omega
  cases maximumActive with
  | false => simpa using hzeroFlag word
  | true =>
      obtain ⟨initial, rfl⟩ := hflag rfl
      have hdiff := hflagDifference depth initial reserve
      have hbase := hzeroFlag (initial ++ [true])
      simp only [ite_true]
      omega

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftReduction
