/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/GroupedBinding
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact verification of the coefficient table used by the refined BMV certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedData
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.QuarticPacking
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetCertificate

/-! Exact arithmetic for the same sparse coefficients used by the sign check. -/

namespace RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks

private def radix : ℤ := 2 ^ 32

private def packGroup (g : Group) : ℤ :=
  (show ℤ from (g.coefficients.map fun (d, c) => c * radix ^ d).sum) <<<
    (32 * (9 * g.x + 1521 * g.u) : ℕ)

private def packColumn (col : Column) : ℤ :=
  ((col.2.map packGroup).sum) <<< (32 * (39 * col.1.1 + 19773 * col.1.2) : ℕ)

private theorem eval_group (g : Group) :
    evalTerms radix (radix ^ 9) (radix ^ 117) (radix ^ 1521) (radix ^ 19773) g.terms =
      packGroup g * radix ^ (117 * g.y + 19773 * g.v) := by
  simp only [evalTerms, Group.terms, List.map_map, Function.comp_def, packGroup, Int.shiftLeft_eq,
    ← List.sum_map_mul_right, Term.eval, Int.cast_id]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  obtain ⟨d,c⟩ := a
  simp only [pow_mul, pow_add, radix]
  ac_rfl

private theorem sum_flatMap_int {α β : Type} (xs : List α) (f : α → List β) (g : β → ℤ) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]

private theorem eval_column (col : Column)
    (h : ∀ g ∈ col.2, g.rateY = col.1) :
    evalTerms radix (radix ^ 9) (radix ^ 117) (radix ^ 1521) (radix ^ 19773)
      (col.2.flatMap Group.terms) = packColumn col := by
  unfold evalTerms
  rw [sum_flatMap_int]
  unfold packColumn
  rw [Int.shiftLeft_eq, pow_mul, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  change evalTerms radix (radix ^ 9) (radix ^ 117) (radix ^ 1521) (radix ^ 19773)
    g.terms = _
  rw [eval_group]
  have hz := h g hg
  have hy : 3 * g.y = col.1.1 := congrArg Prod.fst hz
  have hv : g.v = col.1.2 := congrArg Prod.snd hz
  have he : 117 * g.y + 19773 * g.v = 39 * col.1.1 + 19773 * col.1.2 := by omega
  rw [he]
  rfl

private theorem eval_grouped (c : Certificate) (h : c.checkRates = true) :
    evalTerms radix (radix ^ 9) (radix ^ 117) (radix ^ 1521) (radix ^ 19773) c.terms =
      (c.columns.map packColumn).sum := by
  unfold Certificate.terms evalTerms
  rw [sum_flatMap_int]
  apply congrArg List.sum
  apply List.map_congr_left
  intro col hm
  change evalTerms radix (radix ^ 9) (radix ^ 117) (radix ^ 1521) (radix ^ 19773)
    (col.2.flatMap Group.terms) = packColumn col
  apply eval_column
  intro g hg
  have hcol := List.all_eq_true.mp h col hm
  have hg' := List.all_eq_true.mp hcol g hg
  simp only [Bool.and_eq_true, beq_iff_eq] at hg'
  exact hg'.2

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- This finite check uses all annotated affinity rates.
theorem rates_checked : quartic.checkRates = true := by decide +kernel

private def packPart (negative : Bool) (g : Group) : ℕ :=
  ((g.coefficients.map fun (d, c) =>
    if decide (c < 0) == negative then c.natAbs <<< (32 * d) else 0).sum) <<<
      (32 * (9 * g.x + 1521 * g.u))

private def packPartColumn (negative : Bool) (col : Column) : ℕ :=
  ((col.2.map (packPart negative)).sum) <<< (32 * (39 * col.1.1 + 19773 * col.1.2))

private def evalPackedColumns (cols : List Column) : ℤ :=
  ↑((cols.map (packPartColumn false)).sum) - ↑((cols.map (packPartColumn true)).sum)

private theorem shift_cast (a k : ℕ) : ((a <<< k : ℕ) : ℤ) = (a : ℤ) * 2 ^ k := by
  simp [Nat.shiftLeft_eq]

private theorem packParts_sub (g : Group) :
    (packPart false g : ℤ) - (packPart true g : ℤ) = packGroup g := by
  simp only [packPart, packGroup, shift_cast, Int.shiftLeft_eq, ← sub_mul]
  congr 1
  generalize g.coefficients = cs
  induction cs with
  | nil => simp
  | cons a cs ih =>
    obtain ⟨d, c⟩ := a
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    have hc : (((if decide (c < 0) == false then c.natAbs <<< (32 * d) else 0 : ℕ) : ℤ) -
        ((if decide (c < 0) == true then c.natAbs <<< (32 * d) else 0 : ℕ) : ℤ)) =
        c * radix ^ d := by
      by_cases h : c < 0
      · simp [h, Int.shiftLeft_eq, pow_mul, radix, abs_of_neg h]
      · have hc := le_of_not_gt h
        simp [h, Int.shiftLeft_eq, pow_mul, radix, abs_of_nonneg hc]
    rw [add_sub_add_comm, ih, hc]

private theorem packPartsColumns_sub (col : Column) :
    (packPartColumn false col : ℤ) - (packPartColumn true col : ℤ) = packColumn col := by
  simp only [packPartColumn, packColumn, shift_cast, Int.shiftLeft_eq, ← sub_mul]
  congr 1
  generalize col.2 = gs
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [add_sub_add_comm, ih, packParts_sub]

private theorem evalPackedColumns_eq (cols : List Column) :
    evalPackedColumns cols = (cols.map packColumn).sum := by
  induction cols with
  | nil => simp [evalPackedColumns]
  | cons a cols ih =>
    simp only [evalPackedColumns, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    rw [add_sub_add_comm, ih, packPartsColumns_sub]

set_option maxRecDepth 50000 in
set_option exponentiation.threshold 20000 in
set_option maxHeartbeats 0 in
-- The packed integer evaluation certifies all coefficients together.
private theorem packed_identity :
    evalPackedColumns quartic.columns =
      clearedQuartic radix (radix ^ 9) (radix ^ 117) (radix ^ 1521) (radix ^ 19773) := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- This finite check uses the exponents and coefficient mass of the complete table.
private theorem degree_and_mass :
    quartic.terms.all termFitsQuarticRadix = true ∧ quarticTableMass quartic.terms ≤ 20000000 := by
  decide +kernel

theorem quartic_matches_grouped (p x y u v : ℝ) :
    evalTerms p x y u v quartic.terms = clearedQuartic p x y u v := by
  change evalTerms p x y u v quartic.terms = quarticFormula p x y u v
  exact eval_certified_quartic_table _ degree_and_mass.1 degree_and_mass.2
    ((eval_grouped quartic rates_checked).trans ((evalPackedColumns_eq _).symm.trans
      packed_identity)) p x y u v

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- The finite check verifies the scalar hypotheses for the same table as the mask proofs.
theorem certificateStatic : staticCheck quartic.terms quartic.rootsX quartic.rootsY = true := by
  decide +kernel

end RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks
