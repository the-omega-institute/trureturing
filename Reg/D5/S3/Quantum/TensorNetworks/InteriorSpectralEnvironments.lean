import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments
import Reg.Support.DependentFamily

/-! Whole-proposition source-family attempts. The complete source proposition is retained.
Source-selection evidence is absent under issue #30422; these terms do not assert native validation. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments
open _root_.D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace native_environment_transport
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @native_environment_transport)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @native_environment_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_environment_transport,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@native_environment_transport) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments.native_environment_transport.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments.native_environment_transport.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end native_environment_transport

namespace certificate_positive_targets
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @certificate_positive_targets)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @certificate_positive_targets) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@certificate_positive_targets,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@certificate_positive_targets) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments.certificate_positive_targets.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments.certificate_positive_targets.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end certificate_positive_targets
end Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments
