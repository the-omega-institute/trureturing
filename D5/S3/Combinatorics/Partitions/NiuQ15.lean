/- GID: D5/S3/Combinatorics/Partitions/NiuQ15
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/NiuQ15
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lit/niu2026firstdescent]
   utility: none
   digest: The normalized first-descent law and odd-entry limit in rectangular tableaux. -/

module

public import D5.S3.Combinatorics.Partitions.NiuQ15Tableaux
public import D5.S3.Combinatorics.Partitions.NiuTableauCount
public import D5.S3.Combinatorics.Partitions.NiuQ15Analytic
import Mathlib.Algebra.BigOperators.Fin

/-! Connections to the standard rectangle tableau events. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace NiuQ15

open Analytic

/-- Uniform probability on a finite tableau type as a ratio of cardinalities. -/
noncomputable def eventProbability {α : Type*} [Fintype α] (event : α → Prop) : ℝ :=
  (Nat.card {x : α // event x} : ℝ) / Fintype.card α

/-- Parameter k represents k + 2 rows. At width zero, extend the descent by zero
so that the probabilities are functions of all natural widths. -/
def rectangleDescent (k n : ℕ) (t : StandardTableau (rectangle (k + 1) n)) : ℕ :=
  if hn : 0 < n then firstDescent hn t else 0

noncomputable def rectangleTailProbability (k n r : ℕ) : ℝ :=
  eventProbability fun t : StandardTableau (rectangle (k + 1) n) => r ≤ rectangleDescent k n t

noncomputable def rectanglePointProbability (k n r : ℕ) : ℝ :=
  eventProbability fun t : StandardTableau (rectangle (k + 1) n) => rectangleDescent k n t = r

/-- The entry is one-based, so its value is the descent plus one. -/
noncomputable def rectangleOddEntryProbability (k n : ℕ) : ℝ :=
  eventProbability fun t : StandardTableau (rectangle (k + 1) n) =>
    Odd (rectangleDescent k n t + 1)

theorem rectangleOddEntryProbability_eq {k n : ℕ} (hn : 0 < n) :
    rectangleOddEntryProbability k n =
      eventProbability (fun t : StandardTableau (rectangle (k + 1) n) =>
        Odd ((t.1 (secondRowFirst hn)).val + 1)) := by
  simp only [rectangleOddEntryProbability, rectangleDescent, dite_eq_left hn, firstDescent]

/-- The exact natural-number identity for the shortened and full rectangle counts. -/
def ExactRectangleTailCount (k : ℕ) : Prop :=
  ∀ n r, 0 < n → r ≤ n →
    Fintype.card (StandardTableau (rotatedShape (k + 1) n r)) *
        ((k + 2) * n).descFactorial r =
      Fintype.card (StandardTableau (rectangle (k + 1) n)) *
        tailCoefficient (k + 2) r * n.descFactorial r


open _root_.D5.S3.Combinatorics.Partitions.NiuTableauCount

private theorem eraseRowEnd_rows_eq_deleteRow {k : ℕ} (shape : RowShape k)
    (i : NiuQ15.RemovableRow shape) :
    (eraseRowEnd shape i).rows = deleteRow shape.rows i.1 := by
  funext j
  by_cases h : j = i.1
  · subst j
    simp [eraseRowEnd, deleteRow]
  · simp [eraseRowEnd, deleteRow, h]

/-- The number of standard tableaux of a straight shape is the shifted-node formula. -/
theorem card_standardTableau_eq_shiftedCount {k : ℕ} (hk : 2 ≤ k) (shape : RowShape k) :
    (Fintype.card (StandardTableau shape) : ℚ) = shiftedCount shape.rows := by
  classical
  generalize hn : size shape = n
  induction n using Nat.strong_induction_on generalizing shape with
  | h n ih =>
    by_cases hz : n = 0
    · have hs : size shape = 0 := hn.trans hz
      have hr : shape.rows = fun _ => 0 := by
        funext i
        exact Nat.eq_zero_of_le_zero ((Finset.single_le_sum
          (f := shape.rows) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq hs)
      rw [card_standardTableau_of_size_zero shape hs, Nat.cast_one, hr, shiftedCount_empty]
    · have hp : 0 < size shape := hn.symm ▸ Nat.pos_of_ne_zero hz
      rw [card_standardTableau_eq_sum shape hp, Nat.cast_sum]
      simp_rw [fun i : NiuQ15.RemovableRow shape =>
        ih (size (eraseRowEnd shape i)) (by have := size_eraseRowEnd shape i; omega)
          (eraseRowEnd shape i) rfl, eraseRowEnd_rows_eq_deleteRow]
      rw [shiftedCount_recurrence hk shape.rows shape.antitone_rows hp]
      symm
      refine Finset.sum_subtype _ (fun i => ?_) (fun i => shiftedCount (deleteRow shape.rows i))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl

private theorem vandermonde_last {k : ℕ} (b : Fin (k + 1) → ℚ) :
    vandermonde b = vandermonde (fun i : Fin k => b i.castSucc) *
      ∏ i : Fin k, (b i.castSucc - b (Fin.last k)) := by
  unfold vandermonde
  rw [Fin.prod_univ_castSucc]
  have hempty : Finset.Ioi (Fin.last k) = ∅ := by
    ext i
    simp [not_lt_of_ge (Fin.le_last i)]
  rw [hempty, Finset.prod_empty, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hset : Finset.Ioi i.castSucc =
      insert (Fin.last k) ((Finset.Ioi i).map Fin.castSuccEmb) := by
    ext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.le_last]
  have hnot : Fin.last k ∉ (Finset.Ioi i).map Fin.castSuccEmb := by simp
  rw [hset, Finset.prod_insert hnot, Finset.prod_map]
  exact mul_comm ..

private theorem prod_last_gaps (k r : ℕ) :
    (∏ i : Fin k, (r + (Fin.rev i.castSucc).val : ℚ)) =
      ((r + k).choose k : ℚ) * (k.factorial : ℚ) := by
  have hgap (i : Fin k) : (Fin.rev i.castSucc).val = 1 + (Fin.rev i).val := by
    simp only [Fin.val_rev, Fin.val_castSucc]
    have := i.isLt
    omega
  calc
    _ = ∏ i : Fin k, ((r + 1 + i.val : ℕ) : ℚ) := by
      simp only [hgap, Nat.cast_add, Nat.cast_one, ← add_assoc]
      exact Equiv.prod_comp Fin.revPerm
        (fun i => (r : ℚ) + 1 + (i.val : ℚ))
    _ = ((r + 1).ascFactorial k : ℚ) := by
      rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_fin_eq_prod_range]
      exact Finset.prod_congr rfl fun i hi => dite_eq_left (Finset.mem_range.mp hi)
    _ = _ := by
      rw [← Nat.add_descFactorial_eq_ascFactorial, Nat.descFactorial_eq_factorial_mul_choose,
        Nat.cast_mul, mul_comm]

private theorem rotatedShiftedCount (k n r : ℕ) (hr : r ≤ n) :
    shiftedCount (rotatedShape k n r).rows =
      ((((k + 1) * n - r).factorial : ℚ) *
        (vandermonde (fun i : Fin k => (n + (Fin.rev i.castSucc).val : ℚ)) *
          (((r + k).choose k : ℚ) * (k.factorial : ℚ)))) /
      ((∏ i : Fin k, ((n + (Fin.rev i.castSucc).val).factorial : ℚ)) *
        ((n - r).factorial : ℚ)) := by
  have hupper (i : Fin k) : shiftedNode (rotatedShape k n r).rows i.castSucc =
      n + (Fin.rev i.castSucc).val := by
    simp [shiftedNode, rotatedShape, Fin.castSucc_ne_last]
  have hlast : shiftedNode (rotatedShape k n r).rows (Fin.last k) = n - r := by
    simp [shiftedNode, rotatedShape]
  have hsize : (∑ i, (rotatedShape k n r).rows i) = (k + 1) * n - r := by
    rw [Fin.sum_univ_castSucc]
    simp [rotatedShape, Fin.castSucc_ne_last, Nat.succ_mul]
    omega
  have hdiff (i : Fin k) :
      (shiftedNode (rotatedShape k n r).rows i.castSucc : ℚ) -
        (shiftedNode (rotatedShape k n r).rows (Fin.last k) : ℚ) =
        (r + (Fin.rev i.castSucc).val : ℚ) := by
    rw [hupper, hlast, Nat.cast_add, Nat.cast_sub hr]
    ring
  unfold shiftedCount
  rw [hsize, vandermonde_last, Fin.prod_univ_castSucc]
  simp_rw [hdiff, prod_last_gaps, hupper, hlast, Nat.cast_add]

/-- Exact cardinality ratio for a rectangle and its shortened bottom row. -/
theorem exactRectangleTailCount (k : ℕ) :
    ∀ n r, 0 < n → r ≤ n →
      Fintype.card (StandardTableau (rotatedShape (k + 1) n r)) *
          ((k + 2) * n).descFactorial r =
        Fintype.card (StandardTableau (rectangle (k + 1) n)) *
          tailCoefficient (k + 2) r * n.descFactorial r := by
  change ExactRectangleTailCount k
  intro n r _ hr
  have hrn : r ≤ (k + 2) * n :=
    hr.trans (by rw [show k + 2 = (k + 1) + 1 by omega, Nat.succ_mul]; omega)
  have hrect : rotatedShape (k + 1) n 0 = rectangle (k + 1) n := by
    simp [rotatedShape, rectangle]
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [card_standardTableau_eq_shiftedCount (by omega),
    card_standardTableau_eq_shiftedCount (by omega), ← hrect,
    rotatedShiftedCount _ _ _ hr, rotatedShiftedCount _ _ _ (Nat.zero_le n)]
  have hsize := congrArg (fun x : ℕ => (x : ℚ)) (Nat.factorial_mul_descFactorial hrn)
  have hwidth := congrArg (fun x : ℕ => (x : ℚ)) (Nat.factorial_mul_descFactorial hr)
  push_cast at hsize hwidth
  simp only [Nat.zero_add, Nat.sub_zero, Nat.choose_self, Nat.cast_one, one_mul,
    tailCoefficient, show k + 2 - 1 = k + 1 by omega]
  rw [← hsize, ← hwidth]
  have hfac (a : ℕ) : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hd : (n.descFactorial r : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hr).ne'
  field_simp [hfac, hd, Finset.prod_ne_zero_iff]

theorem rectangleTailProbability_eq {k : ℕ}
    {n : ℕ} (hn : 0 < n) (r : ℕ) :
    rectangleTailProbability k n r = finiteTail (k + 2) n r := by
  unfold rectangleTailProbability eventProbability
  simp only [rectangleDescent, dite_eq_left hn]
  by_cases hr : r ≤ n
  · rw [card_rectangle_tail hn hr, finiteTail_eq_descFactorial (by omega) hr, ← mul_div_assoc]
    have hrect : (0 : ℝ) < Fintype.card (StandardTableau (rectangle (k + 1) n)) := by
      exact_mod_cast rectangle_card_pos (k + 1) n
    have hnr : r ≤ (k + 2) * n := hr.trans <| by
      calc n = 1 * n := (one_mul n).symm
           _ ≤ (k + 2) * n := Nat.mul_le_mul_right n (by omega)
    have hdesc : (0 : ℝ) < ((k + 2) * n).descFactorial r := by
      exact_mod_cast Nat.descFactorial_pos.mpr hnr
    apply (div_eq_div_iff hrect.ne' hdesc.ne').2
    have he := exactRectangleTailCount k n r hn hr
    rw [mul_assoc, mul_comm (Fintype.card (StandardTableau (rectangle (k + 1) n)))] at he
    exact_mod_cast he
  · rw [card_rectangle_tail_of_width_lt hn (by omega), finiteTail_above (by omega),
      Nat.cast_zero, zero_div]

theorem rectangleTailPartition {k : ℕ}
    (n : ℕ) (hn : 0 < n) (r : ℕ) :
    finiteTail (k + 2) n r =
      rectanglePointProbability k n r + finiteTail (k + 2) n (r + 1) := by
  rw [← rectangleTailProbability_eq hn r,
    ← rectangleTailProbability_eq hn (r + 1)]
  unfold rectangleTailProbability rectanglePointProbability eventProbability
  simp only [rectangleDescent, dite_eq_left hn, card_rectangle_tail_eq_point_add_next hn r,
    Nat.cast_add, add_div]

theorem rectangleOddEntryProbability_eq_sum {k n : ℕ} (hn : 0 < n) :
    rectangleOddEntryProbability k n =
      ∑ r ∈ Finset.range (n + 1), if Even r then rectanglePointProbability k n r else 0 := by
  classical
  let α := StandardTableau (rectangle (k + 1) n)
  let descent : α → ℕ := rectangleDescent k n
  let evenIndices := (Finset.range (n + 1)).filter Even
  have hcard :
      ∑ r ∈ evenIndices, Nat.card {t : α // descent t = r} =
        Nat.card {t : α // Odd (descent t + 1)} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext t
    have hwidth : descent t ≤ n := by
      simpa only [descent, rectangleDescent, dite_eq_left hn] using firstDescent_le_width hn t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, evenIndices, Finset.mem_range]
    rw [Nat.even_iff, Nat.odd_iff]
    omega
  rw [← Finset.sum_filter]
  change _ = ∑ r ∈ evenIndices, rectanglePointProbability k n r
  unfold rectangleOddEntryProbability rectanglePointProbability eventProbability
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hcard]

/-- The finite point law includes the zero extension beyond the width. -/
theorem rectanglePointProbability_eq {k : ℕ}
    {n : ℕ} (hn : 0 < n) (r : ℕ) :
    rectanglePointProbability k n r =
      if r ≤ n then rectangleTailProbability k n r *
        (((k : ℝ) + 1) * r * ((n : ℝ) + 1) /
          (((r : ℝ) + 1) * (((k : ℝ) + 2) * n - r)))
      else 0 := by
  split
  · rename_i hr
    rw [rectangleTailProbability_eq hn r]
    have h := point_eq (by omega : 2 ≤ k + 2) (rectangleTailPartition (k := k)) hn hr
    have hrows : (↑(k + 2) : ℝ) = (k : ℝ) + 2 := by push_cast; rfl
    have hrows' : (k : ℝ) + 2 - 1 = (k : ℝ) + 1 := by ring
    simpa only [hrows, hrows'] using h
  · rename_i hr
    exact point_above (rectangleTailPartition (k := k)) hn (by omega)

theorem rectangleOddEntryProbability_eq_alternating {k : ℕ}
    {n : ℕ} (hn : 0 < n) :
    rectangleOddEntryProbability k n =
      ∑' r, (-1 : ℝ) ^ r * finiteTail (k + 2) n r :=
  (rectangleOddEntryProbability_eq_sum hn).trans
    (sum_even_point_eq_alternating (rectangleTailPartition (k := k)) hn)

/-- The first-descent distribution and the odd-entry limit on the actual
rectangle tableaux, from the exact count of the shortened shapes. -/
theorem rectangleQuestion15 (k : ℕ) :
    (∀ r, Tendsto (fun n => rectangleTailProbability k n r) atTop
      (𝓝 (limitTail (k + 2) r))) ∧
    (∀ r, Tendsto (fun n => rectanglePointProbability k n r) atTop
      (𝓝 (limitMass (k + 2) r))) ∧
    HasSum (limitMass (k + 2)) 1 ∧
    Tendsto (rectangleOddEntryProbability k) atTop
      (𝓝 ((((k : ℝ) + 2) / ((k : ℝ) + 3)) ^ (k + 2))) := by
  refine ⟨?_, tendsto_point (by omega) (rectangleTailPartition (k := k)),
    hasSum_limitMass (by omega), ?_⟩
  · intro r
    refine (tendsto_finiteTail (k := k + 2) (by omega) r).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (rectangleTailProbability_eq hn r).symm
  · have h' := (tendsto_alternating_finiteTail (by omega : 2 ≤ k + 2)).congr'
        (show _ =ᶠ[atTop] rectangleOddEntryProbability k by
          filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
          exact (rectangleOddEntryProbability_eq_alternating hn).symm)
    have he : (↑(k + 2) : ℝ) + 1 = (k : ℝ) + 3 := by push_cast; ring
    rw [he] at h'
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h'

end NiuQ15
