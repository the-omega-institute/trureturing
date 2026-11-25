import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A source-bound readout of the integer counts along both axes. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ × ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ d => T d.1 d.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ d => if d = (7, 1) then T d.1 d.2 + 1 else T d.1 d.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ × ℕ), 0 < d.1 → 0 < d.2 →
    (R.readout () () (d.1 + 6, d.2) =
      3 * R.readout () () (d.1 + 5, d.2) + 3 * R.readout () () (d.1 + 4, d.2) -
      15 * R.readout () () (d.1 + 3, d.2) + 4 * R.readout () () (d.1 + 2, d.2) +
      18 * R.readout () () (d.1 + 1, d.2) - 12 * R.readout () () d) ∧
    (R.readout () () (d.1, d.2 + 6) =
      3 * R.readout () () (d.1, d.2 + 5) + 3 * R.readout () () (d.1, d.2 + 4) -
      15 * R.readout () () (d.1, d.2 + 3) + 4 * R.readout () () (d.1, d.2 + 2) +
      18 * R.readout () () (d.1, d.2 + 1) - 12 * R.readout () () d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h (1, 1) (by decide) (by decide)).1
  have good := (result (1, 1) (by decide) (by decide)).1
  change T 7 1 + 1 = 3 * T 6 1 + 3 * T 5 1 - 15 * T 4 1 +
    4 * T 3 1 + 18 * T 2 1 - 12 * T 1 1 at bad
  change T 7 1 = 3 * T 6 1 + 3 * T 5 1 - 15 * T 4 1 +
    4 * T 3 1 + 18 * T 2 1 - 12 * T 1 1 at good
  omega

private def legalDecidable (n k : ℕ) (A : Grid n k) : Decidable (Legal A) := by
  unfold Legal
  infer_instance

private def literalCard (n k : ℕ) : ℕ :=
  letI : DecidablePred (@Legal n k) := legalDecidable n k
  (Finset.univ.filter (@Legal n k)).card

private theorem count_eq_literalCard (n k : ℕ) : T n k = (literalCard n k : ℤ) := by
  letI : DecidablePred (@Legal n k) := legalDecidable n k
  unfold T literalCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 2000000 in
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (1, 1), (2, 1), ?_⟩
  change T 1 1 ≠ T 2 1
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => T d.1 d.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
