import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient TwelveStatePresentation

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Hidden
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Label
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ i => label i) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => (false,0)) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ i j : Hidden, (futureSetoid marked).r i j ↔ R.readout () () i = R.readout () () j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (false,0) (false,1)).mpr rfl
  have he := (future_classes (false,0) (false,1)).mp hh
  norm_num [label] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(),(false,0),(false,1),?_⟩
  change label (false,0) ≠ label (false,1)
  norm_num [label]

def family : Registration arena (type_of% future_classes) where
  actual := realize signature (fun _ _ i => label i) Empty.elim
  bridge := Iff.rfl
  variation := ⟨future_classes,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    future_classes (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => label i) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}, {
      path := #["body","body","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
namespace TwoOccurrences

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Hidden
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Label
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ i => label i) Empty.elim

def changed (k : Fin 2) : Realization signature :=
  realize signature (fun r _ i => if r = k then (false,0) else label i) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ i j : Hidden,
    (futureSetoid marked).r i j ↔ R.readout 0 () i = R.readout 1 () j

private theorem changed_not_law (k : Fin 2) : ¬ arena.Law (changed k) := by
  intro h
  have he := (h (true,0) (true,0)).mp ((futureSetoid marked).refl (true,0))
  fin_cases k <;> norm_num [changed,realize,label] at he <;> cases he

def family : Registration arena (type_of% future_classes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨future_classes,changed 0,changed_not_law 0⟩
  sensitivity := by
    constructor
    · intro k
      refine ⟨changed k,?_,rfl,changed_not_law k⟩
      intro j hj
      funext p i
      simp only [changed,actual,realize]
      rw [if_neg hj]
    · intro i
      exact nomatch i
  dependence := by
    intro k
    refine ⟨(),(false,0),(false,1),?_⟩
    change label (false,0) ≠ label (false,1)
    norm_num [label]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    future_classes (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation.TwoOccurrences.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation.TwoOccurrences.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => label i) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}, {
      path := #["body","body","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end TwoOccurrences

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation
