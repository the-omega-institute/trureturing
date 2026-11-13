import D5.S3.Quantum.Routing.ReversibleQram
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observation of the routing circuit on its full dependent wire family. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.Routing.ReversibleQram

open _root_.D5.S3.Quantum.Routing.ReversibleQram
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, Address n)
    (fun p => Wires p.1) (fun p => Wires p.1)

def actual : Realization signature :=
  realize signature (fun _ p w => route p.1 p.2 w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => clean p.1 false) (fun e => nomatch e)

/-- The other three conjuncts retain their complete original quantifiers and dictionaries. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (n : ℕ) (a i : Address n) (e : Bool),
      leaf n (R.readout () ⟨n, a⟩ (clean n e)) i = if i = a then e else false) ∧
    (type_of% (correctness.2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h.1 0 () () true
  change false = true at hf
  cases hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, ()⟩, false, true, ?_⟩
  change false ≠ true
  decide

def family : Registration arena (type_of% correctness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨correctness, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    correctness (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.ReversibleQram.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.ReversibleQram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p w => route p.1 p.2 w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Wires
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.ReversibleQram
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Routing.ReversibleQram
