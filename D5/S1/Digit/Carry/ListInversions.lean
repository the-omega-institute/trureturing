/- GID: D5/S1/Digit/Carry/ListInversions
   generality: G
   mirror-B: D5/B/S1/Digit/Carry/ListInversions
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.List.Count]
   utility: none
   digest: Head recursion counts smaller tail entries; four local replacement inversion bounds. -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Count

set_option autoImplicit false

namespace D5.S1.Digit.Carry.ListInversions

/-- The number of pairs of positions `p < q` whose entries satisfy `s[p] > s[q]`.
Each recursive step counts exactly the pairs whose first position is the head. -/
def inv : List ℕ → ℕ
  | [] => 0
  | x :: xs => inv xs + xs.countP (fun y => decide (y < x))

private theorem inv_append (L R : List ℕ) :
    inv (L ++ R) = inv L + inv R +
      (L.map fun x => R.countP (fun y => decide (y < x))).sum := by
  induction L with
  | nil => simp [inv]
  | cons x xs ih =>
    simp only [List.cons_append, inv, List.countP_append, List.map_cons, List.sum_cons, ih]
    omega

/-- Split inversions into those outside the window, inside it, and those crossing
its two boundaries. The parenthesized constant is independent of `W`.
The sums are list sums, so repeated window entries retain their multiplicity. -/
theorem inv_window (P W S : List ℕ) :
    inv (P ++ W ++ S) =
      (inv P + inv S +
        (P.map fun p => (S.filter fun q => decide (q < p)).length).sum) +
      inv W + (W.map fun x => (P.filter fun p => decide (x < p)).length).sum +
      (W.map fun x => (S.filter fun q => decide (q < x)).length).sum := by
  simp only [← List.countP_eq_length_filter]
  induction P with
  | nil => simp [inv, inv_append, Nat.add_comm]
  | cons p ps ih =>
    have hboole :
        (W.map fun x => if x < p then 1 else 0).sum =
          W.countP (fun x => decide (x < p)) := by
      simpa [Function.comp_def] using
        (List.countP_flatMap (p := fun x : ℕ => decide (x < p))
          (l := W) (f := fun x => [x])).symm
    simp only [List.cons_append, inv, List.countP_append, List.map_cons, List.sum_cons,
      List.countP_cons, decide_eq_true_eq, List.sum_map_add, ih, hboole]
    omega

section Bounds

variable (P S : List ℕ)

local notation "A" => (fun j : ℕ => P.countP (fun p => decide (j < p)))
local notation "B" => (fun j : ℕ => S.countP (fun q => decide (q < j)))

/-- Replacing the equal pair at `i` by `[i - 2, i + 1]` has an inversion cost
bounded by the occurrences of `i - 1` and `i` outside the window. -/
theorem inv_replace_double (i : ℕ) (hi : 2 < i) :
    inv (P ++ [i - 2, i + 1] ++ S) ≤ inv (P ++ [i, i] ++ S) +
      ((P ++ S).count (i - 1) + (P ++ S).count i) := by
  have astep (j : ℕ) : A j = A (j + 1) + P.count (j + 1) := by
    calc
      A j = (P.filter fun p => decide (j + 1 < p)).countP (fun p => decide (j < p)) +
          (P.filter fun p => !decide (j + 1 < p)).countP (fun p => decide (j < p)) :=
        List.countP_eq_countP_filter_add P _ _
      _ = A (j + 1) + P.count (j + 1) := by
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr
          intro p _
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [List.count_eq_countP]
          apply List.countP_congr
          intro p _
          simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq, beq_iff_eq]
          omega
  have bstep : B (i + 1) = B i + S.count i := by
    calc
      B (i + 1) = (S.filter fun q => decide (q < i)).countP (fun q => decide (q < i + 1)) +
          (S.filter fun q => !decide (q < i)).countP (fun q => decide (q < i + 1)) :=
        List.countP_eq_countP_filter_add S _ _
      _ = B i + S.count i := by
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [List.count_eq_countP]
          apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq, beq_iff_eq]
          omega
  have ha : A (i + 1) ≤ A i := by
    apply List.countP_mono_left
    intro p _ hp
    simp only [decide_eq_true_eq] at hp ⊢
    omega
  have hb : B (i - 2) ≤ B i := by
    apply List.countP_mono_left
    intro q _ hq
    simp only [decide_eq_true_eq] at hq ⊢
    omega
  have h₁ := astep (i - 2)
  have h₂ := astep (i - 1)
  have e₁ : i - 2 + 1 = i - 1 := by omega
  have e₂ : i - 1 + 1 = i := by omega
  rw [e₁] at h₁
  rw [e₂] at h₂
  have hw : ¬i + 1 < i - 2 := by omega
  rw [inv_window, inv_window]
  simp only [inv, List.countP_cons, List.countP_nil, decide_eq_true_eq, hw,
    Nat.lt_irrefl, ite_false, Nat.add_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ← List.countP_eq_length_filter, List.count_append]
  dsimp only at *
  omega

/-- Merging adjacent entries `[a, a + 1]` into `[a + 2]` costs at most the
number of occurrences of `a + 1` outside the window. -/
theorem inv_replace_adjacent (a : ℕ) :
    inv (P ++ [a + 2] ++ S) ≤ inv (P ++ [a, a + 1] ++ S) +
      (P ++ S).count (a + 1) := by
  have bstep : B (a + 2) = B (a + 1) + S.count (a + 1) := by
    calc
      B (a + 2) =
          (S.filter fun q => decide (q < a + 1)).countP (fun q => decide (q < a + 2)) +
          (S.filter fun q => !decide (q < a + 1)).countP (fun q => decide (q < a + 2)) :=
        List.countP_eq_countP_filter_add S _ _
      _ = B (a + 1) + S.count (a + 1) := by
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [List.count_eq_countP]
          apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq, beq_iff_eq]
          omega
  have ha : A (a + 2) ≤ A (a + 1) := by
    apply List.countP_mono_left
    intro p _ hp
    simp only [decide_eq_true_eq] at hp ⊢
    omega
  have hw : ¬a + 1 < a := by omega
  rw [inv_window, inv_window]
  simp only [inv, List.countP_cons, List.countP_nil, decide_eq_true_eq, hw,
    ite_false, Nat.add_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ← List.countP_eq_length_filter, List.count_append]
  dsimp only at *
  omega

/-- Replacing `[1, 1]` by `[2]` costs at most the number of ones outside the window.
Zeros in the suffix are allowed: their contribution is retained in `B 1`. -/
theorem inv_replace_ones :
    inv (P ++ [2] ++ S) ≤ inv (P ++ [1, 1] ++ S) + (P ++ S).count 1 := by
  have bstep : B 2 = B 1 + S.count 1 := by
    calc
      B 2 = (S.filter fun q => decide (q < 1)).countP (fun q => decide (q < 2)) +
          (S.filter fun q => !decide (q < 1)).countP (fun q => decide (q < 2)) :=
        List.countP_eq_countP_filter_add S _ _
      _ = B 1 + S.count 1 := by
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [List.count_eq_countP]
          apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq, beq_iff_eq]
          omega
  have ha : A 2 ≤ A 1 := by
    apply List.countP_mono_left
    intro p _ hp
    simp only [decide_eq_true_eq] at hp ⊢
    omega
  rw [inv_window, inv_window]
  simp only [inv, List.countP_cons, List.countP_nil, decide_eq_true_eq, Nat.lt_irrefl,
    ite_false, Nat.add_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ← List.countP_eq_length_filter, List.count_append]
  dsimp only at *
  omega

/-- Replacing `[2, 2]` by `[1, 3]` costs at most the number of twos outside the window. -/
theorem inv_replace_twos :
    inv (P ++ [1, 3] ++ S) ≤ inv (P ++ [2, 2] ++ S) + (P ++ S).count 2 := by
  have astep : A 1 = A 2 + P.count 2 := by
    calc
      A 1 = (P.filter fun p => decide (2 < p)).countP (fun p => decide (1 < p)) +
          (P.filter fun p => !decide (2 < p)).countP (fun p => decide (1 < p)) :=
        List.countP_eq_countP_filter_add P _ _
      _ = A 2 + P.count 2 := by
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr
          intro p _
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [List.count_eq_countP]
          apply List.countP_congr
          intro p _
          simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq, beq_iff_eq]
          omega
  have bstep : B 3 = B 2 + S.count 2 := by
    calc
      B 3 = (S.filter fun q => decide (q < 2)).countP (fun q => decide (q < 3)) +
          (S.filter fun q => !decide (q < 2)).countP (fun q => decide (q < 3)) :=
        List.countP_eq_countP_filter_add S _ _
      _ = B 2 + S.count 2 := by
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [List.count_eq_countP]
          apply List.countP_congr
          intro q _
          simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq, beq_iff_eq]
          omega
  have ha : A 3 ≤ A 2 := by
    apply List.countP_mono_left
    intro p _ hp
    simp only [decide_eq_true_eq] at hp ⊢
    omega
  have hb : B 1 ≤ B 2 := by
    apply List.countP_mono_left
    intro q _ hq
    simp only [decide_eq_true_eq] at hq ⊢
    omega
  have hw : ¬(3 : ℕ) < 1 := by omega
  rw [inv_window, inv_window]
  simp only [inv, List.countP_cons, List.countP_nil, decide_eq_true_eq, hw,
    Nat.lt_irrefl, ite_false, Nat.add_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ← List.countP_eq_length_filter, List.count_append]
  dsimp only at *
  omega

end Bounds

end D5.S1.Digit.Carry.ListInversions
