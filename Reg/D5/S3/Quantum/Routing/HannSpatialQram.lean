import D5.S3.Quantum.Routing.HannSpatialQram
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.Routing.HannSpatialQram

open _root_.D5.S3.Quantum.Routing.HannSpatialQram
open _root_.D5.S3.Quantum.Routing.ReversibleQram (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, Address n → Bool)
    (fun p => State p.1) (fun p => State p.1)

def actual : Realization signature :=
  realize signature (fun _ p s => query p.1 p.2 s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Every other conjunct retains its entire source telescope. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (type_of% correctness.1) ∧
    (type_of% correctness.2.1) ∧
    (∀ (n : ℕ) (D : Address n → Bool) (a : Address n) (b : Bool),
      R.readout () ⟨n,D⟩ (clean n a b) = clean n a (xor b (D a))) ∧
    (type_of% correctness.2.2.2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := congrArg (fun s : State 0 => s.2.1) (h.2.2.1 0 (fun _ => true) () false)
  change Qutrit.zero = Qutrit.one at hf
  cases hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, fun _ => false⟩, clean 0 () false, clean 0 () true, ?_⟩
  intro h
  have hf := congrArg (fun s : State 0 => s.2.1) h
  change (query 0 (fun _ => false) (clean 0 () false)).2.1 =
    (query 0 (fun _ => false) (clean 0 () true)).2.1 at hf
  rw [correctness.2.2.1, correctness.2.2.1] at hf
  cases hf

def family : Registration arena (type_of% correctness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨correctness, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    correctness (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannSpatialQram.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannSpatialQram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => query p.1 p.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some State
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannSpatialQram
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Routing.HannSpatialQram
