import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9

/-! Full-source-family registration attempt for the exact all-window telescope.
Source-selection evidence is absent under issue #30422. No native validation is asserted. -/

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Prop × ℕ)

def actual : Realization signature := realize signature
  (fun _ _ m => (type_of% (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9.result m), m))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ m => (False,m)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ m : ℕ, (obs.readout () () m).1

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  simp [actual,realize]

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9.result,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ m => (type_of% (_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9.result m),m))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9
