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
initialExhausted: proof_shape=content; consumers=w_leading, initial, initial.eq_1, initial_counts, initial_exhausted_count, initial_from_starts
initial: proof_shape=content; consumers=forward_table, polynomial_relation, result, w, w_leading, count_transfer, initial_counts
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
leading: proof_shape=bind-only; consumers=forward_step, leadingCoordinates, leading_rec, leading_step, w, w_leading
coefficients: proof_shape=bind-only; consumers=polynomialCoordinates, polynomial_relation, recurrence_convolution, leading_polynomial, result
sum_zip_mul: proof_shape=bind-only; consumers=exhausted_step, polynomial_relation
columnRank: proof_shape=bind-only; consumers=rightColumn, representative_data, w, exhausted_step
columnRepresentative: proof_shape=bind-only; consumers=representative_data, checkColumn, exhausted_step
representative_data: proof_shape=bind-only; consumers=w_representative, exhausted_step
w_representative: proof_shape=bind-only; consumers=exhausted_step
exhaustedRank: proof_shape=bind-only; consumers=exhaustedRow
exhaustedRow: proof_shape=content; consumers=w, w_leading
rightColumn: proof_shape=bind-only; consumers=checkColumn, exhausted_step, rightColumn_eq
rightColumn_eq: proof_shape=bind-only; consumers=exhausted_step._simp_4
arithmeticRow: proof_shape=bind-only; consumers=checkColumn, exhausted_step
w: proof_shape=content; consumers=arithmeticRow, checkColumn, exhausted_step, forward_step, forward_table, polynomialCoordinates, polynomial_relation, w_leading
w_leading: proof_shape=bind-only; consumers=forward_step, polynomial_relation
leadingCoefficient: proof_shape=bind-only; consumers=leadingCoordinates, leading_rec, leading_step, recurrence_convolution, leading_polynomial
leadingIndex: proof_shape=bind-only; consumers=leadingCoordinates, leading_rec, leading_step
leadingCoordinates: proof_shape=bind-only; consumers=leading_rec
leading_rec: proof_shape=bind-only; consumers=leading_step
leading_step: proof_shape=bind-only; consumers=forward_step, leading_forward
checkColumn: proof_shape=content; consumers=exhausted_step, stepGroup
stepGroup: proof_shape=content; consumers=exhaustedSteps
exhaustedSteps: proof_shape=content; consumers=exhausted_step
exhausted_step: proof_shape=content; consumers=forward_step
leading_action: proof_shape=bind-only; consumers=forward_step
forward_step: proof_shape=content; consumers=forward_table
forward_table: proof_shape=content; consumers=polynomial_relation
leading_forward: proof_shape=bind-only; consumers=leading_polynomial._simp_1
recurrence_convolution: proof_shape=bind-only; consumers=leading_polynomial
leading_polynomial: proof_shape=bind-only; consumers=polynomial_relation
w_copied: proof_shape=bind-only; consumers=polynomial_relation
polynomialCoordinates: proof_shape=content; consumers=polynomial_relation
polynomial_relation: proof_shape=content; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Recurrence.family._proof_2
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
private def newHistoryRanks : List ℕ :=
  (((List.finRange 60).filter fun k => 72 ≤ (exitRead (columnRepresentative k)).val)
    .map exhaustedRank).eraseDups

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
  rfl

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
        apply List.mem_eraseDups.mpr
        exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, decide_eq_true hk⟩, rfl⟩
      have h := List.all_eq_true.mp polynomialCoordinates (exhaustedRank k) hm
      have hindex (i : Fin 12) : ((i.natAdd 1).castAdd 1).succ = (i.natAdd 2).castAdd 1 :=
        Fin.ext rfl
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
    have hc : horizontal.card = 6 ∧ antidiagonal.card = 6 := by decide +kernel
    rw [hc.1, hc.2] at hf
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
