import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
import Reg.Support.DependentFamily

/-! Whole-proposition source-family attempts. The complete source proposition is retained.
Source-selection evidence is absent under issue #30422; these terms do not assert native validation. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
open _root_.D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace canonical_exclusion_actual_ambiguity
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
  Law obs := obs.readout () () (type_of% @canonical_exclusion_actual_ambiguity)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @canonical_exclusion_actual_ambiguity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_exclusion_actual_ambiguity,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@canonical_exclusion_actual_ambiguity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity.canonical_exclusion_actual_ambiguity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity.canonical_exclusion_actual_ambiguity.source_registration
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
end canonical_exclusion_actual_ambiguity
namespace observed_interior_ambiguity
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
  Law obs := obs.readout () () (type_of% @observed_interior_ambiguity)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @observed_interior_ambiguity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@observed_interior_ambiguity,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@observed_interior_ambiguity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity.observed_interior_ambiguity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity.observed_interior_ambiguity.source_registration
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
end observed_interior_ambiguity

end Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
