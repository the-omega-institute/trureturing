import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A source-bound readout of the literal integer counts along the square diagonal. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence (Grid Legal T)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence (result)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ m => T m m) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ m => if m = 8 then T m m + 1 else T m m)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 1 ≤ m →
    R.readout () () (m + 7) = R.readout () () (m + 6) + 9 * R.readout () () (m + 5) -
      9 * R.readout () () (m + 4) - 26 * R.readout () () (m + 3) +
      26 * R.readout () () (m + 2) + 24 * R.readout () () (m + 1) - 24 * R.readout () () m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 1 (by decide)
  have good := result 1 (by decide)
  change T 8 8 + 1 = T 7 7 + 9 * T 6 6 - 9 * T 5 5 - 26 * T 4 4 +
    26 * T 3 3 + 24 * T 2 2 - 24 * T 1 1 at bad
  change T 8 8 = T 7 7 + 9 * T 6 6 - 9 * T 5 5 - 26 * T 4 4 +
    26 * T 3 3 + 24 * T 2 2 - 24 * T 1 1 at good
  omega

private def legalDecidable (n k : ℕ) (a : Grid n k) : Decidable (Legal a) := by
  unfold Legal
  infer_instance

private def literalCard (n k : ℕ) : ℕ :=
  letI : DecidablePred (@Legal n k) := legalDecidable n k
  (Finset.univ.filter (@Legal n k)).card

private theorem count_eq_literalCard (n k : ℕ) : T n k = (literalCard n k : ℤ) := by
  let _ : DecidablePred (@Legal n k) := legalDecidable n k
  unfold T literalCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 2000000 in
private theorem small_diagonal_counts : T 0 0 = 4 ∧ T 1 1 = 20 := by
  rw [count_eq_literalCard 0 0, count_eq_literalCard 1 1]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change T 0 0 ≠ T 1 1
  rw [small_diagonal_counts.1, small_diagonal_counts.2]
  decide

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => T m m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence
