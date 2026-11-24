/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.polynomial_relation
   digest: The integer recurrence for canonical two-defect width-seven arrays. -/

/-
admission_basis: open-problem-resolution (#33283; Proved)
escape_witness: polynomial_relation computes the order-twelve vector relation at shift two
initialExhausted: proof_shape=bind-only; consumers=w_leading, initial, initial.eq_1, initial_counts, initial_exhausted_count, initial_from_starts
initial: proof_shape=bind-only; consumers=count_transfer, forward_table, initial.eq_1, initial_counts, polynomial_relation, result, w, w.eq_1, w_copied, w_leading, w_new, w_representative, Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Count.arena, Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Count.audit, Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Count.family, Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Count.family._proof_1, Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Count.rejected_law
terminal: proof_shape=bind-only; consumers=result, count_transfer, terminal_eq
next_valid: proof_shape=bind-only; consumers=count_transfer
initial_valid: proof_shape=bind-only; consumers=count_transfer
terminal_eq: proof_shape=bind-only; consumers=count_transfer
headWeight: proof_shape=bind-only; consumers=head_weight_eq, initial_exhausted_count, initial_from_starts, rep_weight
head_weight_eq: proof_shape=bind-only; consumers=initial_exhausted_count
fresh_start_count: proof_shape=bind-only; consumers=initial_exhausted_count
rep_weight: proof_shape=bind-only; consumers=initial_exhausted_count
initial_from_starts: proof_shape=content; consumers=initial_exhausted_count
initial_exhausted_count: proof_shape=content; consumers=initial_counts
initial_counts: proof_shape=content; consumers=count_transfer
count_transfer: proof_shape=content; consumers=result, Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Count.family._proof_2
a: proof_shape=bind-only; consumers=result, scale_count
leading: proof_shape=bind-only; consumers=forward_step, leading.eq_1, leadingCoordinates, leadingCoordinates._proof_1, leading_polynomial, leading_polynomial._simp_2, leading_rec, leading_step, polynomial_relation, w, w.eq_1, w_copied, w_leading, w_new, w_representative
coefficients: proof_shape=bind-only; consumers=polynomialCoordinates, polynomial_relation, recurrence_convolution, leading_polynomial, result
sum_zip_mul: proof_shape=bind-only; consumers=exhausted_step, polynomial_relation
columnRank: proof_shape=bind-only; consumers=exhausted_step, exhausted_step._proof_1, exhausted_step._proof_2, exhausted_step._proof_3, polynomial_relation, polynomial_relation._proof_2, representative_data, representative_data._proof_1, representative_data._proof_10, representative_data._proof_11, representative_data._proof_12, representative_data._proof_13, representative_data._proof_14, representative_data._proof_15, representative_data._proof_16, representative_data._proof_17, representative_data._proof_18, representative_data._proof_19, representative_data._proof_2, representative_data._proof_20, representative_data._proof_21, representative_data._proof_22, representative_data._proof_23, representative_data._proof_24, representative_data._proof_25, representative_data._proof_26, representative_data._proof_27, representative_data._proof_28, representative_data._proof_29, representative_data._proof_3, representative_data._proof_30, representative_data._proof_31, representative_data._proof_32, representative_data._proof_33, representative_data._proof_34, representative_data._proof_35, representative_data._proof_36, representative_data._proof_37, representative_data._proof_38, representative_data._proof_39, representative_data._proof_4, representative_data._proof_40, representative_data._proof_41, representative_data._proof_42, representative_data._proof_43, representative_data._proof_44, representative_data._proof_45, representative_data._proof_46, representative_data._proof_47, representative_data._proof_48, representative_data._proof_49, representative_data._proof_5, representative_data._proof_50, representative_data._proof_51, representative_data._proof_52, representative_data._proof_53, representative_data._proof_54, representative_data._proof_55, representative_data._proof_56, representative_data._proof_57, representative_data._proof_58, representative_data._proof_59, representative_data._proof_6, representative_data._proof_60, representative_data._proof_61, representative_data._proof_62, representative_data._proof_63, representative_data._proof_64, representative_data._proof_65, representative_data._proof_66, representative_data._proof_67, representative_data._proof_68, representative_data._proof_69, representative_data._proof_7, representative_data._proof_70, representative_data._proof_71, representative_data._proof_72, representative_data._proof_73, representative_data._proof_74, representative_data._proof_75, representative_data._proof_76, representative_data._proof_77, representative_data._proof_78, representative_data._proof_79, representative_data._proof_8, representative_data._proof_80, representative_data._proof_81, representative_data._proof_82, representative_data._proof_83, representative_data._proof_84, representative_data._proof_85, representative_data._proof_86, representative_data._proof_87, representative_data._proof_88, representative_data._proof_89, representative_data._proof_9, representative_data._proof_90, representative_data._proof_91, representative_data._proof_92, representative_data._proof_93, representative_data._proof_94, representative_data._proof_95, representative_data._proof_96, rightColumn, rightColumn_eq, w, w.eq_1, w_copied, w_leading, w_new, w_representative
columnRepresentative: proof_shape=bind-only; consumers=checkColumn, exhausted_step, newHistoryRanks, polynomial_relation, polynomial_relation._proof_2, representative_data, representative_data._proof_1, representative_data._proof_10, representative_data._proof_11, representative_data._proof_12, representative_data._proof_13, representative_data._proof_14, representative_data._proof_15, representative_data._proof_16, representative_data._proof_17, representative_data._proof_18, representative_data._proof_19, representative_data._proof_2, representative_data._proof_20, representative_data._proof_21, representative_data._proof_22, representative_data._proof_23, representative_data._proof_24, representative_data._proof_25, representative_data._proof_26, representative_data._proof_27, representative_data._proof_28, representative_data._proof_29, representative_data._proof_3, representative_data._proof_30, representative_data._proof_31, representative_data._proof_32, representative_data._proof_33, representative_data._proof_34, representative_data._proof_35, representative_data._proof_36, representative_data._proof_37, representative_data._proof_38, representative_data._proof_39, representative_data._proof_4, representative_data._proof_40, representative_data._proof_41, representative_data._proof_42, representative_data._proof_43, representative_data._proof_44, representative_data._proof_45, representative_data._proof_46, representative_data._proof_47, representative_data._proof_48, representative_data._proof_49, representative_data._proof_5, representative_data._proof_50, representative_data._proof_51, representative_data._proof_52, representative_data._proof_53, representative_data._proof_54, representative_data._proof_55, representative_data._proof_56, representative_data._proof_57, representative_data._proof_58, representative_data._proof_59, representative_data._proof_6, representative_data._proof_60, representative_data._proof_61, representative_data._proof_62, representative_data._proof_63, representative_data._proof_64, representative_data._proof_65, representative_data._proof_66, representative_data._proof_67, representative_data._proof_68, representative_data._proof_69, representative_data._proof_7, representative_data._proof_70, representative_data._proof_71, representative_data._proof_72, representative_data._proof_73, representative_data._proof_74, representative_data._proof_75, representative_data._proof_76, representative_data._proof_77, representative_data._proof_78, representative_data._proof_79, representative_data._proof_8, representative_data._proof_80, representative_data._proof_81, representative_data._proof_82, representative_data._proof_83, representative_data._proof_84, representative_data._proof_85, representative_data._proof_86, representative_data._proof_87, representative_data._proof_88, representative_data._proof_89, representative_data._proof_9, representative_data._proof_90, representative_data._proof_91, representative_data._proof_92, representative_data._proof_93, representative_data._proof_94, representative_data._proof_95, representative_data._proof_96, rightColumn_at_representative, rightColumn_at_representative._proof_1, rightColumn_at_representative._proof_10, rightColumn_at_representative._proof_11, rightColumn_at_representative._proof_12, rightColumn_at_representative._proof_13, rightColumn_at_representative._proof_14, rightColumn_at_representative._proof_15, rightColumn_at_representative._proof_16, rightColumn_at_representative._proof_17, rightColumn_at_representative._proof_18, rightColumn_at_representative._proof_19, rightColumn_at_representative._proof_2, rightColumn_at_representative._proof_20, rightColumn_at_representative._proof_21, rightColumn_at_representative._proof_22, rightColumn_at_representative._proof_23, rightColumn_at_representative._proof_24, rightColumn_at_representative._proof_25, rightColumn_at_representative._proof_26, rightColumn_at_representative._proof_27, rightColumn_at_representative._proof_28, rightColumn_at_representative._proof_29, rightColumn_at_representative._proof_3, rightColumn_at_representative._proof_30, rightColumn_at_representative._proof_31, rightColumn_at_representative._proof_32, rightColumn_at_representative._proof_33, rightColumn_at_representative._proof_34, rightColumn_at_representative._proof_35, rightColumn_at_representative._proof_36, rightColumn_at_representative._proof_37, rightColumn_at_representative._proof_38, rightColumn_at_representative._proof_39, rightColumn_at_representative._proof_4, rightColumn_at_representative._proof_40, rightColumn_at_representative._proof_41, rightColumn_at_representative._proof_42, rightColumn_at_representative._proof_43, rightColumn_at_representative._proof_44, rightColumn_at_representative._proof_45, rightColumn_at_representative._proof_46, rightColumn_at_representative._proof_47, rightColumn_at_representative._proof_48, rightColumn_at_representative._proof_49, rightColumn_at_representative._proof_5, rightColumn_at_representative._proof_50, rightColumn_at_representative._proof_51, rightColumn_at_representative._proof_52, rightColumn_at_representative._proof_53, rightColumn_at_representative._proof_54, rightColumn_at_representative._proof_55, rightColumn_at_representative._proof_56, rightColumn_at_representative._proof_57, rightColumn_at_representative._proof_58, rightColumn_at_representative._proof_59, rightColumn_at_representative._proof_6, rightColumn_at_representative._proof_60, rightColumn_at_representative._proof_7, rightColumn_at_representative._proof_8, rightColumn_at_representative._proof_9, rightColumn_eq, stepGroup, w_new, w_representative
representative_data: proof_shape=bind-only; consumers=exhausted_step, polynomial_relation, rightColumn_eq, w_new, w_representative
w_representative: proof_shape=bind-only; consumers=exhausted_step, w_new
exhaustedRank: proof_shape=bind-only; consumers=newHistoryRanks, polynomial_relation, w, w.eq_1, w_copied, w_leading, w_new, w_representative
exhaustedRow: proof_shape=content; consumers=polynomialCoordinates, polynomialCoordinates._proof_1, polynomial_relation, w, w.eq_1, w_copied, w_leading, w_new, w_representative
rightColumn: proof_shape=bind-only; consumers=checkColumn, exhausted_step, rightColumn_at_representative, rightColumn_at_representative._proof_1, rightColumn_at_representative._proof_10, rightColumn_at_representative._proof_11, rightColumn_at_representative._proof_12, rightColumn_at_representative._proof_13, rightColumn_at_representative._proof_14, rightColumn_at_representative._proof_15, rightColumn_at_representative._proof_16, rightColumn_at_representative._proof_17, rightColumn_at_representative._proof_18, rightColumn_at_representative._proof_19, rightColumn_at_representative._proof_2, rightColumn_at_representative._proof_20, rightColumn_at_representative._proof_21, rightColumn_at_representative._proof_22, rightColumn_at_representative._proof_23, rightColumn_at_representative._proof_24, rightColumn_at_representative._proof_25, rightColumn_at_representative._proof_26, rightColumn_at_representative._proof_27, rightColumn_at_representative._proof_28, rightColumn_at_representative._proof_29, rightColumn_at_representative._proof_3, rightColumn_at_representative._proof_30, rightColumn_at_representative._proof_31, rightColumn_at_representative._proof_32, rightColumn_at_representative._proof_33, rightColumn_at_representative._proof_34, rightColumn_at_representative._proof_35, rightColumn_at_representative._proof_36, rightColumn_at_representative._proof_37, rightColumn_at_representative._proof_38, rightColumn_at_representative._proof_39, rightColumn_at_representative._proof_4, rightColumn_at_representative._proof_40, rightColumn_at_representative._proof_41, rightColumn_at_representative._proof_42, rightColumn_at_representative._proof_43, rightColumn_at_representative._proof_44, rightColumn_at_representative._proof_45, rightColumn_at_representative._proof_46, rightColumn_at_representative._proof_47, rightColumn_at_representative._proof_48, rightColumn_at_representative._proof_49, rightColumn_at_representative._proof_5, rightColumn_at_representative._proof_50, rightColumn_at_representative._proof_51, rightColumn_at_representative._proof_52, rightColumn_at_representative._proof_53, rightColumn_at_representative._proof_54, rightColumn_at_representative._proof_55, rightColumn_at_representative._proof_56, rightColumn_at_representative._proof_57, rightColumn_at_representative._proof_58, rightColumn_at_representative._proof_59, rightColumn_at_representative._proof_6, rightColumn_at_representative._proof_60, rightColumn_at_representative._proof_7, rightColumn_at_representative._proof_8, rightColumn_at_representative._proof_9, rightColumn_eq
rightColumn_eq: proof_shape=bind-only; consumers=exhausted_step
arithmeticRow: proof_shape=bind-only; consumers=checkColumn, exhausted_step
w: proof_shape=content; consumers=arithmeticRow, arithmeticRow.eq_1, checkColumn, exhausted_step, forward_step, forward_table, polynomial_relation, w.eq_1, w_copied, w_leading, w_new, w_representative
w_leading: proof_shape=bind-only; consumers=forward_step, polynomial_relation
leadingCoefficient: proof_shape=bind-only; consumers=leadingCoordinates, leading_rec, leading_step, recurrence_convolution, leading_polynomial
leadingIndex: proof_shape=bind-only; consumers=leadingCoordinates, leading_rec, leading_step
leadingCoordinates: proof_shape=bind-only; consumers=leading_rec
leading_rec: proof_shape=bind-only; consumers=leading_step
leading_step: proof_shape=bind-only; consumers=forward_step, leading_forward
checkColumn: proof_shape=content; consumers=exhausted_step, stepGroup
stepGroup: proof_shape=bind-only; consumers=exhaustedSteps, exhaustedSteps._proof_1, exhaustedSteps._proof_10, exhaustedSteps._proof_2, exhaustedSteps._proof_3, exhaustedSteps._proof_4, exhaustedSteps._proof_5, exhaustedSteps._proof_6, exhaustedSteps._proof_7, exhaustedSteps._proof_8, exhaustedSteps._proof_9
exhaustedSteps: proof_shape=content; consumers=exhausted_step
exhausted_step: proof_shape=content; consumers=forward_step
leading_action: proof_shape=bind-only; consumers=forward_step
forward_step: proof_shape=content; consumers=forward_table
forward_table: proof_shape=content; consumers=polynomial_relation
recurrence_convolution: proof_shape=bind-only; consumers=leading_polynomial
leading_polynomial: proof_shape=bind-only; consumers=polynomial_relation
w_copied: proof_shape=bind-only; consumers=forward_step, polynomial_relation
polynomialCoordinates: proof_shape=content; consumers=polynomial_relation
polynomial_relation: proof_shape=content; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Recurrence.family._proof_2
newHistoryRanks: proof_shape=bind-only; consumers=polynomialCoordinates, polynomialCoordinates._proof_1, polynomial_relation
rightColumn_at_representative: proof_shape=bind-only; consumers=rightColumn_eq
w_new: proof_shape=bind-only; consumers=polynomial_relation
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Starts
import Mathlib.Data.Matrix.Block
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Eval
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Mul
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.ReduceEval

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
set_option Elab.async false

open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
  (bondDefects defects literalCount constant_defects relabel_defects forward forward_eq forward_shift)
open HardinA229585StripData (Boundary Row horizontal antidiagonal boundary cross)
open HardinA229693StripTransfer
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (canonical_exists_unique)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (canonical_pattern_card)

private def initialExhausted (i : Fin 96) : ℤ :=
  Fin.addCases (fun j : Fin 56 => HardinA229585StripData.initial (j.natAdd 16) - 6)
    (fun _ : Fin 40 => 12) i

def initial : Fin 168 → ℤ :=
  Fin.append HardinA229585StripData.initial initialExhausted

def terminal : Fin 168 → ℤ :=
  Fin.append (0 : Fin 72 → ℤ) (1 : Fin 96 → ℤ)

private theorem next_valid (p : Boundary) (d : ℕ) (hp : HardinA229635State.Valid p d) (r : Row)
    (hr : cross p r + bondDefects horizontal r r ≤ d) :
    HardinA229635State.Valid (boundary r) (d - (cross p r + bondDefects horizontal r r)) := by
  have hd := ((valid_parts p d).mp hp).1
  have ht := horizontal_cons (r 0) (boundary r)
  rw [show Fin.cons (r 0) (boundary r) = r from Fin.cons_self_tail r] at ht
  change HardinA229635State.h (boundary r) + (d - (cross p r + bondDefects horizontal r r)) ≤ 2
  omega

private theorem initial_valid (r : Row) (hr : bondDefects horizontal r r ≤ 2) :
    HardinA229635State.Valid (boundary r) (2 - bondDefects horizontal r r) := by
  have ht := horizontal_cons (r 0) (boundary r)
  rw [show Fin.cons (r 0) (boundary r) = r from Fin.cons_self_tail r] at ht
  change HardinA229635State.h (boundary r) + (2 - bondDefects horizontal r r) ≤ 2
  omega

private theorem terminal_eq (p : Boundary) (d : ℕ) :
    terminal (cl p d) = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0 <;> simp [cl, terminal, hd]

private def headWeight (p : Boundary) : ℤ :=
  if HardinA229635State.h p = 1 then 1 else
  if HardinA229635State.h p = 2 then 2 else 0

private theorem head_weight_eq (p : Boundary) :
    (∑ x : Fin 3, if bondDefects horizontal (Fin.cons x p) (Fin.cons x p) = 2
      then (1 : ℤ) else 0) = headWeight p := by
  simp_rw [horizontal_cons]
  unfold headWeight
  by_cases h₁ : HardinA229635State.h p = 1
  · simp only [h₁, ite_true]
    have h (x : Fin 3) :
        ((if x = p 0 then (1 : ℕ) else 0) + 1 = 2) ↔ x = p 0 := by
      split_ifs <;> simp_all
    simp [h, Finset.sum_ite_eq']
  · by_cases h₂ : HardinA229635State.h p = 2
    · simp only [h₁, h₂, ite_false, ite_true]
      have h (x : Fin 3) :
          ((if x = p 0 then (1 : ℕ) else 0) + 2 = 2) ↔ x ≠ p 0 := by
        split_ifs <;> simp_all
      simp_rw [h]
      rw [show (fun x : Fin 3 => if x ≠ p 0 then (1 : ℤ) else 0) =
          fun x => 1 - (if x = p 0 then 1 else 0) by
        funext x
        by_cases hx : x = p 0 <;> simp [hx], Finset.sum_sub_distrib]
      simp
    · simp only [h₁, h₂, ite_false]
      apply Finset.sum_eq_zero
      intro x _
      split_ifs with hx <;> omega

private theorem fresh_start_count (i : Fin 96) :
    (∑ p : Boundary, if HardinA229635State.h p ≤ 2 ∧ HardinA229635State.fresh p = i
      then (1 : ℤ) else 0) = 6 := by
  have h := HardinA229635State.start_count (i.natAdd 31)
  rw [HardinA229635Starts.checked_starts, HardinA229635Starts.start_tallies] at h
  simp only [Fin.val_natAdd, show ¬ 31 + i.val < 31 by omega, ite_false] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : HardinA229635State.h p ≤ 2
  · have hn : ¬ HardinA229635State.h p + (2 - HardinA229635State.h p) ≤ 1 := by omega
    simp only [hp, true_and, HardinA229635State.cl, hn, ite_false]
    by_cases he : HardinA229635State.fresh p = i
    · simp only [he, ite_true]
    · simp only [he, (Fin.natAdd_injective 96 31).ne he, ite_false]
  · simp [hp]

private theorem rep_weight (p : Boundary) (hp : HardinA229635State.h p ≤ 2)
    (j : Fin 96) :
    (if exhaustedClass p = j then headWeight p else 0) =
      (let q := HardinA229635State.rep (HardinA229635State.fresh p)
       if exhaustedClass q = j then headWeight q else 0) := by
  obtain ⟨q, ⟨hn, e, rfl⟩, _⟩ := canonical_exists_unique p
  have hp' := (HardinA229635State.h_relabel e p).symm ▸ hp
  have h := HardinA229635Laws.representatives_complete (e ∘ p) hn hp'
  rw [fresh_relabel] at h
  rw [h]
  simp only [headWeight, HardinA229635State.h_relabel, exhausted_relabel]

-- Only the reindexing and head weights are checked here. The 96 fibre sizes
-- come from the frozen start certificate.
set_option maxRecDepth 14000 in
set_option maxHeartbeats 4000000 in
private theorem initial_from_starts (j : Fin 96) :
    (∑ i : Fin 96, if exhaustedClass (HardinA229635State.rep i) = j
      then headWeight (HardinA229635State.rep i) * 6 else 0) = initialExhausted j := by
  revert j
  decide +kernel

private theorem initial_exhausted_count (j : Fin 96) :
    (∑ r : Row, if bondDefects horizontal r r = 2 ∧ exhaustedClass (boundary r) = j
      then (1 : ℤ) else 0) = initialExhausted j := by
  rw [← (Fin.consEquiv (fun _ : Fin 7 => Fin 3)).sum_comp, Fintype.sum_prod_type_right]
  change (∑ p : Boundary, ∑ x : Fin 3,
    if bondDefects horizontal (Fin.cons x p) (Fin.cons x p) = 2 ∧ exhaustedClass p = j
    then (1 : ℤ) else 0) = _
  calc
    _ = ∑ p : Boundary, if exhaustedClass p = j then headWeight p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : exhaustedClass p = j
      · simp only [hp, and_true, ite_true, head_weight_eq]
      · simp only [hp, and_false, ite_false, Finset.sum_const_zero]
    _ = ∑ p ∈ Finset.univ.filter (fun p => HardinA229635State.h p ≤ 2),
        (if exhaustedClass (HardinA229635State.rep (HardinA229635State.fresh p)) = j
          then headWeight (HardinA229635State.rep (HardinA229635State.fresh p)) else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : HardinA229635State.h p ≤ 2
      · simpa only [hp, ite_true] using rep_weight p hp j
      · simp [headWeight, hp, show HardinA229635State.h p ≠ 1 by omega,
          show HardinA229635State.h p ≠ 2 by omega]
    _ = _ := by
      let weight (i : Fin 96) : ℤ :=
        if exhaustedClass (HardinA229635State.rep i) = j
        then headWeight (HardinA229635State.rep i) else 0
      change (∑ p ∈ Finset.univ.filter (fun p => HardinA229635State.h p ≤ 2),
        weight (HardinA229635State.fresh p)) = _
      rw [← Finset.sum_fiberwise' _ HardinA229635State.fresh weight, ← initial_from_starts j]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]
      have hf := fresh_start_count i
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hf
      rw [hf, mul_comm]
      dsimp only [weight]
      split_ifs <;> simp

private theorem initial_counts (s : Fin 168) :
    (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s
      then (1 : ℤ) else 0) = initial s := by
  induction s using Fin.addCases (m := 72) (n := 96) with
  | left j =>
    simp_rw [active_cut]
    simpa only [show 0 < (2 : ℕ) by decide, true_and, Nat.reduceSub, initial,
      Fin.append_left] using HardinA229585Strip.finite_certificate.2.2.2.2.1 j
  | right j =>
    simp_rw [exhausted_cut]
    simpa only [initial, Fin.append_right] using initial_exhausted_count j

/-- The exact two-defect labelled count as a matrix coefficient. -/
theorem count_transfer (n : ℕ) :
    (D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.literalCount
      (q := 3) horizontal antidiagonal 2 (n + 1) : ℤ) =
      dotProduct initial ((T ^ n).mulVec terminal) := by
  exact D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.lumped_count
    horizontal antidiagonal boundary cross HardinA229635State.Valid cl T initial terminal 2
    HardinA229585Strip.edge (fun p d _ => terminal_eq p d) next_valid
    (fun p d hp s => transition_counts p d s hp) initial_valid initial_counts n

/-- Canonical arrays with exactly two monochromatic bonds. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun f : Fin n × Fin 7 → Fin 3 => HardinA229585Strip.Normal f) :=
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn.arrayCanonicalDecidable
  (Finset.univ.filter fun f : Fin n × Fin 7 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => f (i, j)) = 2 ∧
      HardinA229585Strip.Normal f).card

private def leadingCoefficient : Fin 8 → ℤ := by
  exact (fun (c : Fin 8 → ℤ)
    (_ : HardinA229585StripData.W 10 = ∑ k : Fin 8,
      c k • HardinA229585StripData.W ⟨2 + k.val, by omega⟩) => c) _
    HardinA229585Strip.finite_certificate.2.2.2.2.2.2

-- Generate the four continuation rows from the frozen order-eight relation.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
private def leading : Fin 15 → Fin 72 → ℤ :=
  let continuation : Array (Array ℤ) := by
    run_tac
      let coefficients ← Lean.Meta.withTransparency .all <|
        (List.finRange 8).mapM fun k => do
          let entry := Lean.mkApp (Lean.mkConst ``leadingCoefficient) (Lean.toExpr k)
          let positive : Nat ← Lean.Meta.reduceEval (Lean.mkApp (Lean.mkConst ``Int.toNat) entry)
          let negative : Nat ← Lean.Meta.reduceEval
            (Lean.mkApp (Lean.mkConst ``Int.toNat) (Lean.mkApp (Lean.mkConst ``Int.neg) entry))
          pure ((positive : Int) - (negative : Int))
      let coefficients := coefficients.toArray
      let mut columns : Array (Array Int) := #[]
      for j in List.finRange 72 do
        let column ← Lean.Meta.savingCache do
          let values ← Lean.Meta.withTransparency .all <|
            (List.finRange 11).mapM fun i => do
              let entry := Lean.mkApp2 (Lean.mkConst ``HardinA229585StripData.W)
                (Lean.toExpr i) (Lean.toExpr j)
              let value : Nat ← Lean.Meta.reduceEval (Lean.mkApp (Lean.mkConst ``Int.toNat) entry)
              pure (value : Int)
          let mut values := values.toArray
          for i in [11:15] do
            let mut next := 0
            for k in [0:8] do
              next := next + coefficients[k]! * values[i - 8 + k]!
            values := values.push next
          pure (values.extract 11 15)
        columns := columns.push column
      (← Lean.Elab.Tactic.getMainGoal).assign (Lean.toExpr columns)
  Fin.append HardinA229585StripData.W (fun (i : Fin 4) j => (continuation[j.val]!)[i.val]!)

private def coefficients : Fin 12 → ℤ := ![-531441000, 1913187600, -2986698420, 2659094568, -1494608922, 554666940, -138045627, 22918302, -2474469, 165456, -6345, 126]

private theorem sum_zip_mul {n : ℕ} (u v : Fin n → ℤ) :
    (List.zipWith (· * ·) (List.ofFn u) (List.ofFn v)).sum = dotProduct u v := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.zipWith_map, List.zipWith_self,
    ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

private def columnRank (j : Fin 96) : Fin 60 :=
  (eval% (let keys := (List.ofFn exitRead).eraseDups
    Array.ofFn fun i : Fin 96 => Fin.ofNat 60 (keys.idxOf (exitRead i))) : Array (Fin 60))[j.val]!

private def columnRepresentative (k : Fin 60) : Fin 96 :=
  (eval% (List.ofFn fun k : Fin 60 => Fin.ofNat 96
    ((List.ofFn columnRank).idxOf k)) : List (Fin 96))[k.val]!

-- Pack the existing transfer columns into radix-32 words at their representatives.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
private def rightColumn (j : Fin 96) : List ℤ :=
  let columns : Array ℕ := by
    run_tac
      let mut columns : Array Lean.Expr := #[]
      for k in List.finRange 60 do
        let representative := columnRepresentative k
        let key : Nat ← Lean.Meta.withTransparency .all <| Lean.Meta.reduceEval
          (Lean.mkApp2 (Lean.mkConst ``Fin.val) (Lean.mkRawNatLit 108)
            (Lean.mkApp (Lean.mkConst ``exitRead) (Lean.toExpr representative)))
        if key < 72 then
          columns := columns.push (Lean.mkRawNatLit 0)
          continue
        let j := representative.natAdd 72
        let word ← Lean.Meta.savingCache do
          let mut word := 0
          for i in List.finRange 168 do
            let entry := Lean.mkApp2 (Lean.mkConst ``T) (Lean.toExpr i) (Lean.toExpr j)
            let digit : Nat ← Lean.Meta.withTransparency .all <|
              Lean.Meta.reduceEval (Lean.mkApp (Lean.mkConst ``Int.toNat) entry)
            unless digit < 32 do
              throwError "column {j.val}, row {i.val} exceeds one radix-32 digit"
            word := word + (digit <<< (5 * i.val))
          pure word
        columns := columns.push (Lean.mkRawNatLit word)
      (← Lean.Elab.Tactic.getMainGoal).assign
        (← Lean.Meta.mkArrayLit (Lean.mkConst ``Nat) columns.toList)
  let word := columns[(columnRank j).val]!
  List.ofFn fun i : Fin 168 => (((word >>> (5 * i.val)) % 32 : ℕ) : ℤ)

set_option maxRecDepth 10000 in
private theorem representative_data (j : Fin 96) :
    columnRank (columnRepresentative (columnRank j)) = columnRank j ∧
    exitRead (columnRepresentative (columnRank j)) = exitRead j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem rightColumn_at_representative (k : Fin 60)
    (hk : 72 ≤ (exitRead (columnRepresentative k)).val) :
    List.ofFn (fun i : Fin 168 => T i ((columnRepresentative k).natAdd 72)) =
      rightColumn (columnRepresentative k) := by
  fin_cases k <;> revert hk <;> decide +kernel

private theorem rightColumn_eq (j : Fin 96) (hj : 72 ≤ (exitRead j).val) :
    List.ofFn (fun i : Fin 168 => T i (j.natAdd 72)) = rightColumn j := by
  rcases representative_data j with ⟨hrank, hexit⟩
  calc
    _ = List.ofFn (fun i : Fin 168 => T i ((columnRepresentative (columnRank j)).natAdd 72)) :=
      congrArg List.ofFn (funext (new_column_congr j _ hj hexit.symm))
    _ = rightColumn (columnRepresentative (columnRank j)) :=
      rightColumn_at_representative _ (hexit.symm ▸ hj)
    _ = rightColumn j := by
      unfold rightColumn
      rw [hrank]

private def exhaustedRank (k : Fin 60) : ℕ :=
  let packed : ℕ := eval% (
    let novel := (List.finRange 60).filter fun k => 72 ≤ (exitRead (columnRepresentative k)).val
    Nat.ofDigits 64 (List.ofFn fun k : Fin 60 =>
      let j := novel.idxOf k
      if j = 34 then 30 else if 34 < j ∧ j < novel.length then j - 1 else j))
  (packed >>> (6 * k.val)) % 64

-- Rows after the initial vector, restricted to exhausted coordinates with their own column.
private def exhaustedRow (i : Fin 14) (r : ℕ) : ℤ :=
  let values : Array (Array ℤ) := #[
    #[1380, 1302, 1398, 1374,
      1374, 1308, 3582, 1452,
      3660, 3690, 3786, 1446,
      1350, 1494, 1302, 1308,
      1422, 3948, 4002, 3840,
      1350, 3732, 1278, 1494,
      180, 144, 180, 144,
      180, 144, 180, 144,
      180, 144, 144],
    #[68718, 63492, 56460, 64122,
      64374, 66684, 359250, 72912,
      348780, 348576, 338142, 68082,
      63120, 58506, 62130, 67092,
      58620, 329358, 339594, 337686,
      64980, 348978, 60330, 59730,
      5724, 4752, 4932, 4068,
      4788, 4212, 5292, 3852,
      6120, 4680, 4392],
    #[2831886, 2557908, 2233620, 2640906,
      2676546, 2863368, 23028066, 3147084,
      21670380, 21823776, 19943118, 2879694,
      2539152, 2247030, 2637126, 2806776,
      2281320, 17755164, 19518858, 20332440,
      2750940, 21368394, 2602170, 2323926,
      184140, 152496, 150660, 127116,
      146340, 131436, 166860, 118476,
      196560, 148176, 139536],
    #[110901906, 98736948, 85346244, 103322034,
      105025302, 114432696, 1218239838, 126311616,
      1120258404, 1143238212, 1002331314, 114334902,
      98108820, 84361662, 105248430, 110894724,
      86139720, 835005348, 964099098, 1038120300,
      109401192, 1095931782, 104872914, 87767442,
      5886756, 4870368, 4765068, 4041252,
      4630932, 4175388, 5319108, 3757428,
      6282360, 4720680, 4452408],
    #[4199557914, 3702130920, 3176028792, 3908472426,
      3976442442, 4385925792, 57941320626, 4855687236,
      52373492892, 54091076508, 46024489494, 4364180694,
      3679610652, 3100495158, 4033781046, 4221221040,
      3177412596, 36492811740, 43771224366, 48245918544,
      4182205608, 51007321458, 4045847778, 3237915870,
      188028540, 155531664, 151899300, 128952324,
      147641940, 133209684, 169832700, 119854404,
      200669400, 150691104, 142176384],
    #[155161854450, 135798338700, 115836639084, 144286871562,
      146858372406, 163413806400, 2573858147958, 181303880472,
      2295999883332, 2395205611164, 1992290232186, 162129032838,
      134984798028, 112020203070, 150309716958, 156524757372,
      115110338328, 1520275547520, 1879901465994, 2108252882160,
      155551321728, 2229835036734, 151466331834, 117314110674,
      6005294964, 4967207712, 4849678332, 4117779828,
      4713868548, 4253589612, 5423867892, 3827066292,
      6409105560, 4812303960, 4540684392],
    #[5627653189146, 4898192996232, 4159650456216, 5229832016322,
      5324553138330, 5964332360688, 108993164030946, 6627897586044,
      96216542391564, 101214300469860, 82703638963638, 5904461012238,
      4869090286884, 3992939661294, 5486613095502, 5692430074824,
      4111813496628, 61197455276820, 77586545562390, 88182200758608,
      5670010496304, 93265570014786, 5548198044474, 4190859428814,
      191797144380, 158641585776, 154879447140, 131509620036,
      150542888580, 135846178596, 173226190140, 122224142916,
      204694714440, 153692667216, 145019550096],
    #[201202806733434, 174359352163572, 147545108464788, 186883896677922,
      190310062976406, 214289305884144, 4454400117236598, 238426577987040,
      3899108125368468, 4130337726082476, 3326928831733338, 211775495112702,
      173329547873724, 140789323375398, 197141786947494, 203949163506852,
      145230154066944, 2400241083036048, 3107161190914650, 3569359795953048,
      203509760083632, 3774328661986542, 199895852016738, 148031305215570,
      6125617000116, 5066688475008, 4946486099868, 4200131566692,
      4807990370772, 4338627295788, 5532491262708, 3903568697988,
      6537543900120, 4908621335400, 4631629877208],
    #[7111631776682034, 6141055174938576, 5181603562377216, 6602785492162410,
      6725009156352858, 7604108667837072, 177114037081642002, 8469039838061556,
      153955078595737020, 164048348112179796, 130588998960532518, 7504607147065830,
      6104957036904180, 4920122896825014, 6996087920680470, 7220976505648992,
      5082528053463948, 92233371087877500, 121529663889368886, 140830084962208800,
      7215776145984384, 148874229655066242, 7109187903909234, 5180824225054062,
      195639959915100, 161819864591184, 157980579154020, 134143679778804,
      153557331938100, 138566926994724, 176696675398620, 124672037520564,
      208796107426920, 156771469548864, 147924975117024],
    #[249028575131368242, 214413311595375036, 180478839214433340, 231131290257467514,
      235443594006825462, 267137262688177872, 6889830233804901414, 297764716710931848,
      5953895366091922116, 6376200948326213388, 5025805857576252234, 263345677097813478,
      213157918831635324, 170667648816513534, 245790431261532414, 253211655381045804,
      176511623863441464, 3485937596981083128, 4663603113427616490, 5443660317502139256,
      253327673006594928, 5752780847372017710, 250205561179357770, 179933112077347026,
      6248349284810004, 5168202841229472, 5045582286586332, 4284280319815188,
      4904312775435108, 4425549830966412, 5643338457355092, 3981774906087732,
      6668530489920600, 5006966938653240, 4724427916350792],
    #[8652830351266803546, 7431768700419259656, 6242845178013132312, 8028664700506486578,
      8179444644293543994, 9307196397777734928, 263269220623816015170, 10381294814421848364,
      226372210329806578476, 243481483454911718004, 190310555601128294838, 9166500161819165502,
      7388400472323365556, 5882865264388399518, 8563849238990440638, 8808492993123417912,
      6090495875325746676, 129952418190890268420, 176169430982621488806, 206905929897046750992,
      8821208218212289728, 218585513213931105378, 8730504042701293098, 6208781214612669102,
      199559788068985020, 165062068373361456, 161145804890453220, 136831346920473156,
      156633939958642020, 141343211852284356, 180236950437337020, 127169928104649156,
      212979536822036520, 159912514489348656, 150888784625726256],
    #[298690122775220251722, 256002398043554895876, 214673095830392580132, 277076788838717046930,
      282309302665154274390, 322016895781252060752, 9911259978836295771126, 359384905273051977264,
      8485600822002368133876, 9161425800869604574284, 7109225209756337678298, 316897335930915138222,
      254512753777713305628, 201686784845927316534, 296309386199805171318, 304366336432979374260,
      208988333441419797648, 4788687090147326124912, 6567552673847723539386, 7754247938835738344808,
      305060191610725698192, 8189434854851496321870, 302451037728195837042, 213053887018079507538,
      6373540791196442676, 5271752565127510848, 5146674892004047068, 4370119728580718532,
      5002574948528749812, 4514219672056015788, 5756407970401182708, 4061553318183088548,
      6802140750423272280, 5107286098205178120, 4819086211254583608],
    #[10252933247636780430114, 8771738784098364999072, 7344532867927421206800, 9509031256196258171514,
      9689462354390937393114, 11075477370294450927312, 368461572595190590214898, 12366777466142391317796,
      314281488124999689646428, 340436598212032736561460, 262522764733254505543494, 10891975565665556049366,
      8720823408171527183508, 6882211679731177557510, 10191625231806262217574, 10456725589763375258064,
      7136814732214621621500, 174719434451153360633100, 242096507700458948570934, 287154165410942918129856,
      10488076295989061820960, 303180882913672776927234, 10413935493650142634530, 7275850746332516690094,
      203558154755340943260, 168369240807661772304, 164374509661068055140, 139572889921543632084,
      159772245491577207060, 144175154091034480164, 183848165826820646940, 129717895457283483924,
      217246780882429635240, 163116510512892472224, 153911982173910776064],
    #[350241734731328265333474, 299171966172566206433292, 250165130390782457573196, 324770626271610842147946,
      330958491427238097331638, 378988418653993573424784, 13551015423406402699193862, 423354794737866152419224,
      11520447842324619589728996, 12515760724824872783653068, 9598281740308168560537066, 372489191866882427252598,
      297439186122410464378620, 233880404733774585685998, 348754060525438519907310, 357469232995976715247356,
      242695588078659981260520, 6320247971778669765211272, 8838048342882855587054922, 10525118378068958256317880,
      358764033565693265991408, 11109479883159529076458158, 356689646183326388766426, 247429642161654015030738,
      6501240633096725573844, 5377377049719549592032, 5249793319372823395932, 4457679154120649948148,
      5102806200004349118468, 4604666273489124225612, 5871742978790285999892, 4142930326967430161172,
      6938427993757659921240, 5209615341934804082520, 4915641103197855527592]
  ]
  let row := values[i.val]!
  row[r]!

private def w (i : Fin 15) (j : Fin 168) : ℤ :=
  if h : i.val = 0 then initial j
  else Fin.addCases (leading i) (fun k =>
    if hk : (exitRead k).val < 72 then leading i ⟨(exitRead k).val, hk⟩
    else exhaustedRow (Fin.subNat 1 i (Nat.pos_of_ne_zero h)) (exhaustedRank (columnRank k))) j

private def arithmeticRow (i : Fin 15) : List ℤ :=
  List.ofFn (w i)

private theorem w_leading (i : Fin 15) (j : Fin 72) : w i (j.castAdd 96) = leading i j := by
  induction i using Fin.cases with
  | zero =>
    simp only [w, Fin.val_zero, dite_true, initial, Fin.append_left, leading]
    exact congrFun HardinA229585Strip.finite_certificate.2.2.2.2.2.1.1.symm j
  | succ i =>
    simp only [w, Fin.val_succ, Nat.succ_ne_zero, dite_false, Fin.addCases_left]

private def leadingIndex (i : Fin 5) (k : Fin 8) : Fin 15 :=
  ⟨2 + i.val + k.val, by omega⟩

-- Check the continuation rows beyond the last frozen forward vector.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem leadingCoordinates :
    (List.finRange 4).all (fun i => (List.finRange 72).all fun j =>
      leading (i.succ.natAdd 10) j ==
        (List.ofFn fun k : Fin 8 => leadingCoefficient k *
          leading (leadingIndex i.succ k) j).sum) = true := by
  decide +kernel

private theorem leading_rec (i : Fin 5) :
    leading (i.natAdd 10) = ∑ k : Fin 8, leadingCoefficient k • leading (leadingIndex i k) := by
  induction i using Fin.cases with
  | zero =>
    exact HardinA229585Strip.finite_certificate.2.2.2.2.2.2
  | succ i =>
    funext j
    have h := List.all_eq_true.mp
      (List.all_eq_true.mp leadingCoordinates i (List.mem_finRange i)) j (List.mem_finRange j)
    simpa only [beq_iff_eq, List.sum_ofFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

private theorem leading_step (i : Fin 14) :
    leading i.succ = Matrix.vecMul (leading i.castSucc) HardinA229585StripData.T := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases h : i.val < 10
    · let k : Fin 10 := ⟨i.val, h⟩
      have hi : k.castAdd 4 = i := Fin.ext rfl
      rw [← hi]
      have hs : (k.castAdd 4).succ = k.succ.castAdd 4 := Fin.ext rfl
      have hc : (k.castAdd 4).castSucc = k.castSucc.castAdd 4 := Fin.ext rfl
      simp only [hs, hc, leading, Fin.append_left]
      exact HardinA229585Strip.finite_certificate.2.2.2.2.2.1.2 k
    · let k : Fin 4 := ⟨i.val - 10, by omega⟩
      have hp : i.castSucc = k.castSucc.natAdd 10 := Fin.ext (by dsimp [k]; omega)
      have hs : i.succ = k.succ.natAdd 10 := Fin.ext (by dsimp [k]; omega)
      rw [hp, hs, leading_rec, leading_rec, Matrix.sum_vecMul]
      simp only [Matrix.smul_vecMul]
      apply Finset.sum_congr rfl
      intro j _
      let x : Fin 14 := ⟨(leadingIndex k.castSucc j).val, by
        dsimp [leadingIndex]
        omega⟩
      have hx : x < i := by
        change x.val < i.val
        dsimp [x, leadingIndex, k]
        omega
      have hc : x.castSucc = leadingIndex k.castSucc j := Fin.ext rfl
      have hn : x.succ = leadingIndex k.succ j := Fin.ext (by
        simp [x, leadingIndex]
        omega)
      rw [← hc, ← hn, ih x hx]

private theorem w_representative (i : Fin 15) (hi : i.val ≠ 0) (j : Fin 96) :
    w i ((columnRepresentative (columnRank j)).natAdd 72) = w i (j.natAdd 72) := by
  rcases representative_data j with ⟨hrank, hexit⟩
  simp only [w, hi, dite_false, Fin.addCases_right, hexit, hrank]

private def checkColumn (k : Fin 60) : Bool :=
  let j := columnRepresentative k
  let column := rightColumn j
  (List.finRange 14).all fun i =>
    w i.succ (j.natAdd 72) ==
      (List.zipWith (· * ·) (arithmeticRow i.castSucc) column).sum

private def stepGroup (g : Fin 10) : Bool :=
  ((((List.finRange 60).drop (6 * g.val)).take 6).filter
    (fun k => 72 ≤ (exitRead (columnRepresentative k)).val)).all checkColumn

-- Check one destination from each class of equal right columns.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem exhaustedSteps (g : Fin 10) : stepGroup g = true := by
  fin_cases g <;> decide +kernel

private theorem exhausted_step (i : Fin 14) (j : Fin 96)
    (hj : 72 ≤ (exitRead j).val) :
    w i.succ (j.natAdd 72) = Matrix.vecMul (w i.castSucc) T (j.natAdd 72) := by
  let k := columnRank j
  let g : Fin 10 := ⟨k.val / 6, by omega⟩
  have hm : k ∈ ((List.finRange 60).drop (6 * g.val)).take 6 := by
    rw [List.mem_iff_getElem]
    refine ⟨k.val % 6, by simp [g]; omega, ?_⟩
    apply Fin.ext
    simp [List.getElem_take, List.getElem_drop, g]
    omega
  have hk : 72 ≤ (exitRead (columnRepresentative k)).val := by
    rw [(representative_data j).2]
    exact hj
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp (exhaustedSteps g) k (List.mem_filter.mpr ⟨hm, decide_eq_true hk⟩))
    i (List.mem_finRange i)
  change (w i.succ ((columnRepresentative k).natAdd 72) ==
    (List.zipWith (· * ·) (arithmeticRow i.castSucc) (rightColumn (columnRepresentative k))).sum)
      = true at h
  have hcol : rightColumn (columnRepresentative k) = rightColumn j := by
    unfold rightColumn
    rw [(representative_data j).1]
  rw [beq_iff_eq, w_representative i.succ (Nat.succ_ne_zero _) j, hcol] at h
  simpa only [arithmeticRow, ← rightColumn_eq j hj, sum_zip_mul, Matrix.vecMul] using h

private theorem leading_action (v : Fin 168 → ℤ) (j : Fin 72) :
    Matrix.vecMul v T (j.castAdd 96) =
      Matrix.vecMul (fun k : Fin 72 => v (k.castAdd 96)) HardinA229585StripData.T j := by
  let e : Fin 72 ⊕ Fin 96 ≃ Fin 168 := finSumFinEquiv
  simp only [T, Matrix.reindex, Equiv.coe_fn_mk]
  rw [Matrix.submatrix_vecMul_equiv _ v e.symm e.symm, Matrix.vecMul_fromBlocks]
  have hj : e.symm (j.castAdd 96) = Sum.inl j :=
    finSumFinEquiv_symm_apply_castAdd (m := 72) (n := 96) j
  simp only [Function.comp_apply, Equiv.symm_symm, hj, Sum.elim_inl, Matrix.vecMul_zero,
    add_zero]
  rfl

private theorem w_copied (i : Fin 15) (hi : i.val ≠ 0) (j : Fin 96)
    (hj : (exitRead j).val < 72) :
    w i (j.natAdd 72) = leading i ⟨(exitRead j).val, hj⟩ := by
  simp only [w, hi, dite_false, Fin.addCases_right, hj, dite_true]

private theorem forward_step (i : Fin 14) :
    w i.succ = Matrix.vecMul (w i.castSucc) T := by
  funext j
  induction j using Fin.addCases (m := 72) (n := 96) with
  | left j =>
    rw [leading_action]
    simpa only [w_leading] using congrFun (leading_step i) j
  | right j =>
    by_cases hj : (exitRead j).val < 72
    · rw [w_copied _ (Nat.succ_ne_zero _) j hj]
      have hcol : Matrix.vecMul (w i.castSucc) T (j.natAdd 72) =
          Matrix.vecMul (w i.castSucc) T ((⟨(exitRead j).val, hj⟩ : Fin 72).castAdd 96) := by
        simp only [Matrix.vecMul, dotProduct, copied_column j hj]
      rw [hcol, leading_action]
      simpa only [w_leading] using congrFun (leading_step i) ⟨(exitRead j).val, hj⟩
    · exact exhausted_step i j (Nat.le_of_not_gt hj)

private theorem forward_table (i : Fin 15) : forward T initial i.val = w i := by
  let rows := List.ofFn w
  have hchain : rows.IsChain (fun u v => Matrix.vecMul u T = v) := by
    exact List.isChain_ofFn.mpr fun k hk =>
      (forward_step ⟨k, by omega⟩).symm
  have hi : i.val < rows.length := by simpa only [rows, List.length_ofFn] using i.isLt
  have he := hchain.iterate_eq_of_apply_eq i.val hi
  simp only [rows, List.getElem_ofFn] at he
  exact he

-- The five shifted order-eight residuals give the order-twelve residual.
private theorem recurrence_convolution (v : ℕ → ℤ)
    (h : ∀ n : ℕ, n ≤ 4 → v (n + 2 + 8) =
      ∑ k : Fin 8, leadingCoefficient k * v (n + 2 + k.val)) :
    v 14 = ∑ k : Fin 12, coefficients k * v (2 + k.val) := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  norm_num only [leadingCoefficient, coefficients, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_one, Nat.add_zero, Nat.reduceAdd] at h0 h1 h2 h3 h4 ⊢
  linear_combination h4 - 42 * h3 + 351 * h2 - 972 * h1 + 810 * h0

private theorem leading_polynomial (j : Fin 72) :
    leading (Fin.last 14) j =
      ∑ k : Fin 12, coefficients k * leading ((k.natAdd 2).castAdd 1) j := by
  let v (n : ℕ) := leading (Fin.ofNat 15 n) j
  have hv (i : Fin 15) : leading i j = v i.val :=
    congrArg (fun t => leading t j) (Fin.ext (Nat.mod_eq_of_lt i.isLt)).symm
  have h (n : ℕ) (hn : n ≤ 4) :
      v (n + 2 + 8) = ∑ k : Fin 8, leadingCoefficient k * v (n + 2 + k.val) := by
    let i : Fin 5 := ⟨n, by omega⟩
    have hr := congrFun (leading_rec i) j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv, Fin.val_natAdd,
      leadingIndex, i, Nat.add_comm 2 n, Nat.add_comm 10 n, Nat.add_assoc] using hr
  simpa only [hv, Fin.val_last, Fin.val_castAdd, Fin.val_natAdd] using
    recurrence_convolution v h

private def newHistoryRanks : List ℕ :=
  let keys := (List.finRange 60).filter fun k => 72 ≤ (exitRead (columnRepresentative k)).val
  (keys.map exhaustedRank).eraseDups

set_option maxRecDepth 14000 in
set_option maxHeartbeats 3000000 in
private theorem polynomialCoordinates :
    newHistoryRanks.all (fun r =>
      exhaustedRow (Fin.last 13) r ==
        (List.zipWith (· * ·) (List.ofFn coefficients)
          (List.ofFn fun k : Fin 12 => exhaustedRow ((k.natAdd 1).castAdd 1) r)).sum) = true := by
  decide +kernel

private theorem w_new (i : Fin 14) (j : Fin 96) (hj : 72 ≤ (exitRead j).val) :
    w i.succ (j.natAdd 72) = exhaustedRow i (exhaustedRank (columnRank j)) := by
  rw [← w_representative i.succ (Nat.succ_ne_zero _) j]
  rcases representative_data j with ⟨hrank, hexit⟩
  have h := Nat.not_lt.mpr hj
  simp only [w, Fin.val_succ, Nat.succ_ne_zero, dite_false, Fin.addCases_right, hexit, hrank, h]
  all_goals rfl

private theorem polynomial_relation :
    forward T initial (2 + 12) =
      ∑ j : Fin 12, coefficients j • forward T initial (2 + j.val) := by
  change forward T initial (Fin.last 14).val = _
  rw [forward_table (Fin.last 14)]
  simp_rw [show ∀ j : Fin 12, forward T initial (2 + j.val) =
      w ((j.natAdd 2).castAdd 1) from fun j => forward_table ((j.natAdd 2).castAdd 1)]
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  induction k using Fin.addCases (m := 72) (n := 96) with
  | left j =>
    simpa only [w_leading] using leading_polynomial j
  | right j =>
    by_cases hj : (exitRead j).val < 72
    · have hlast : (Fin.last 14).val ≠ 0 := by decide
      have hindex (i : Fin 12) : ((i.natAdd 2).castAdd 1).val ≠ 0 := by
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        omega
      simpa only [w_copied _ hlast j hj, fun i => w_copied _ (hindex i) j hj] using
        leading_polynomial ⟨(exitRead j).val, hj⟩
    · let k := columnRank j
      have hk : 72 ≤ (exitRead (columnRepresentative k)).val := by
        rw [(representative_data j).2]
        exact Nat.le_of_not_gt hj
      have hm : exhaustedRank k ∈ newHistoryRanks := by
        unfold newHistoryRanks
        apply List.mem_eraseDups.mpr
        exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, decide_eq_true hk⟩, rfl⟩
      have h := List.all_eq_true.mp polynomialCoordinates (exhaustedRank k) hm
      have hindex (i : Fin 12) : ((i.natAdd 1).castAdd 1).succ = (i.natAdd 2).castAdd 1 := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_natAdd, Fin.val_castAdd]
        omega
      change w (Fin.last 13).succ (j.natAdd 72) = _
      simp only [← hindex, fun i => w_new i j (Nat.le_of_not_gt hj)]
      simpa only [beq_iff_eq, sum_zip_mul, dotProduct] using h

private theorem scale_count (m : ℕ) :
    literalCount (q := 3) horizontal antidiagonal 2 (m + 1) = 6 * a (m + 1) := by
  classical
  let s : (Fin (m + 1) × Fin 7 → Fin 3) → Prop := fun f =>
    defects horizontal antidiagonal (List.ofFn fun i j => f (i, j)) = 2
  have hinv (e : Equiv.Perm (Fin 3)) (f : Fin (m + 1) × Fin 7 → Fin 3) :
      s (e ∘ f) ↔ s f := by
    change defects horizontal antidiagonal _ = 2 ↔ _
    rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
      (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      relabel_defects]
  have huse (f : Fin (m + 1) × Fin 7 → Fin 3) (hf : s f) : ∃ i j, f i ≠ f j := by
    by_contra h
    push Not at h
    have he : f = fun _ => f (0, 0) := funext fun i => h i (0, 0)
    change defects horizontal antidiagonal _ = 2 at hf
    rw [he, List.ofFn_const, constant_defects] at hf
    have hc : horizontal.card = 6 := by
      rw [horizontal, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
      exact fun _ _ h => Fin.castSucc_inj.mp (congrArg Prod.fst h)
    rw [hc] at hf
    omega
  have h := @canonical_pattern_card (Fin (m + 1) × Fin 7) inferInstance
    (HardinA229585Strip.cellOrder (m + 1)) s hinv huse
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, s] at h
  unfold literalCount a HardinA229585Strip.Normal
  convert h using 1

attribute [local irreducible] a T initial terminal

/-- Hardin's order-twelve recurrence from row count fifteen. -/
theorem result (t : ℕ) :
    (a (t + 15) : ℤ) = 126 * a (t + 14) - 6345 * a (t + 13) + 165456 * a (t + 12) - 2474469 * a (t + 11) +
      22918302 * a (t + 10) - 138045627 * a (t + 9) + 554666940 * a (t + 8) - 1494608922 * a (t + 7) +
      2659094568 * a (t + 6) - 2986698420 * a (t + 5) + 1913187600 * a (t + 4) - 531441000 * a (t + 3) := by
  have bridge (n : ℕ) :
      dotProduct initial ((T ^ n).mulVec terminal) = 6 * (a (n + 1) : ℤ) := by
    rw [← count_transfer, scale_count]
    push_cast
    rfl
  have h := forward_shift T initial terminal 12 2 coefficients polynomial_relation t
  simp_rw [bridge] at h
  norm_num only [coefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Nat.add_assoc,
    Nat.add_zero, Nat.reduceAdd] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
