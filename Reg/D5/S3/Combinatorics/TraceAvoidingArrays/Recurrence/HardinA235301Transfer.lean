import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
import Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readout of literal stress-three counts. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Count

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ h w => (C 3 3 h w : ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ h w =>
    if h = 1 ∧ w = 1 then (C 3 3 h w : ℤ) + 1 else (C 3 3 h w : ℤ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h w : ℕ), 0 < h → 0 < w →
    R.readout () h w = evalHist (path h) (fun s => value w s.mask)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law 1 1 (by decide) (by decide)
  have good := count_transfer 1 1 (by decide) (by decide)
  dsimp [rejected, realize] at bad
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (C 3 3 1 1 : ℤ) ≠ (C 3 3 1 2 : ℤ)
  rw [_root_.Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding.small_counts.1, _root_.Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding.small_counts.2]
  decide

def family : Registration arena (type_of% @count_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_transfer) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer.Count.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer.Count.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h w => (C 3 3 h w : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Count

namespace Normalize

private abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ α : Type, Hist α) (fun p => p.1 → ℤ) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ p f => evalHist p.2 f) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ p f => evalHist p.2 f + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type} [DecidableEq α] (key : α → ℕ) (xs : Hist α) (f : α → ℤ),
    evalHist (normalize key xs) f = R.readout () ⟨α, xs⟩ f

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := @law Unit inferInstance (fun _ => 0) [] (fun _ => 0)
  change evalHist (normalize (fun (_ : Unit) => 0) []) (fun _ => 0) =
    evalHist [] (fun (_ : Unit) => 0) + 1 at bad
  rw [eval_normalize] at bad
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨⟨Unit, [((), 1)]⟩, (fun _ => 0), (fun _ => 1), by decide⟩

def family : Registration arena (type_of% @eval_normalize) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eval_normalize, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@eval_normalize) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer.Normalize.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer.Normalize.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => evalHist p.2 f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalize

namespace Parity

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Bool)

private def actual : Realization signature :=
  realize signature (fun _ _ i => par i) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, par (n + 1) = !(R.readout () () n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact (by decide : par 2 ≠ true) (law 1)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  exact ⟨(), 0, 1, (by decide +kernel : par 0 ≠ par 1)⟩

def family : Registration arena (type_of% @par_succ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨par_succ, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@par_succ) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer.Parity.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer.Parity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => par i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Parity

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
