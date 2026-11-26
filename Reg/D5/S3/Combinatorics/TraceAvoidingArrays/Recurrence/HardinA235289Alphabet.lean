import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet
import Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A source-bound readout of the canonical rectangular counts. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence (T)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet (inPair literalCount result)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
  (count_eq_literalCard)
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ n k => T n k) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ n k => if n = 1 ∧ k = 1 then T n k + 1 else T n k)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k i : ℕ), 1 ≤ n → 1 ≤ k → (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
    literalCount n k i = R.readout () n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 1 1 1 (by decide) (by decide) (Or.inl rfl)
  change T 1 1 = T 1 1 + 1 at bad
  omega

set_option maxRecDepth 64000 in
set_option maxHeartbeats 2000000 in
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨1, 1, 2, ?_⟩
  change T 1 1 ≠ T 1 2
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => T n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace InPair

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin (n + 1))
    (fun n => Fin (n + 2))

private def actual : Realization signature :=
  realize signature (fun _ _ j => j.castSucc) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ j => j.succ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (x : Fin (n + 2)),
    ∃ j : Fin (n + 1), x = R.readout () n j ∨ x = j.succ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨j, hj | hj⟩ := @h 0 0
  · exact (Fin.succ_ne_zero j) hj.symm
  · exact (Fin.succ_ne_zero j) hj.symm

def family : Registration arena (type_of% @inPair) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inPair, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨1, 0, 1, by decide⟩

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@inPair) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet.InPair.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet.InPair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => j.castSucc) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end InPair

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet
