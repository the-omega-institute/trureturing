import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction
import Reg.Support.DependentFamily

/-! Whole-proposition source-family attempts. The complete source proposition is retained.
Source-selection evidence is absent under issue #30422; these terms do not assert native validation. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction
open _root_.D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace monomial_evaluation
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
abbrev arena.{u} : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @monomial_evaluation.{u})
private lemma rejected_law.{u} : ¬ arena.{u}.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration.{u} : Registration arena.{u} (type_of% @monomial_evaluation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@monomial_evaluation.{u},rejected,rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law.{u}⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration.{u} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@monomial_evaluation.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction.monomial_evaluation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction.monomial_evaluation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
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
end monomial_evaluation

namespace coefficients_evaluation
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
abbrev arena.{u} : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @coefficients_evaluation.{u})
private lemma rejected_law.{u} : ¬ arena.{u}.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration.{u} : Registration arena.{u} (type_of% @coefficients_evaluation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficients_evaluation.{u},rejected,rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law.{u}⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration.{u} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@coefficients_evaluation.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction.coefficients_evaluation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction.coefficients_evaluation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
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
end coefficients_evaluation

end Reg.D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction
