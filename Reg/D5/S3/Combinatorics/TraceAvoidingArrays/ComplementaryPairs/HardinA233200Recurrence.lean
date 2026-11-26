import D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Audit of the signed lag readout in the full positive-height recurrence. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ+ (fun _ => Fin 22) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ _ j => lagCoefficient j) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ j => lagCoefficient j + if j = 21 then 1 else 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ+) (hn : 24 ≤ n.val),
    (a n : ℤ) =
      ∑ j : Fin 22, R.readout () n j * (a ⟨n.val - (j.val+1), by omega⟩ : ℤ)

private theorem two_rows_positive : 0 < (a 2 : ℤ) := by
  exact_mod_cast (show 0 < a 2 from by
    unfold a
    apply Finset.card_pos.mpr
    let A : Fin 2 × Fin 6 → Fin 8 := fun p => ⟨(2*p.1.val + p.2.val) % 3, by omega⟩
    exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      unfold Legal rowLegal bonds rho
      decide +kernel⟩⟩)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let n : ℕ+ := 24
  have hn : 24 ≤ n.val := by decide
  let count (j : Fin 22) : ℤ := a ⟨n.val - (j.val+1), by omega⟩
  have ha := result n hn
  have hb := h n hn
  change (a n : ℤ) = ∑ j, lagCoefficient j * count j at ha
  change (a n : ℤ) = ∑ j, (lagCoefficient j + if j = 21 then 1 else 0) * count j at hb
  simp_rw [add_mul] at hb
  rw [Finset.sum_add_distrib, ← ha] at hb
  have he : (∑ j : Fin 22, (if j = 21 then (1 : ℤ) else 0) * count j) = (a 2 : ℤ) := by
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    rfl
  rw [he] at hb
  linarith [two_rows_positive]

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨24, 0, 1, ?_⟩
    change lagCoefficient 0 ≠ lagCoefficient 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => lagCoefficient j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200Recurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200Recurrence
