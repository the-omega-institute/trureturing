import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory LeanInformationAudit
open scoped BigOperators Classical Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveSupportPresentation
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
universe u

@[reducible] def signature : Signature where
  Params := Σ _t : ℤ, ℕ
  State p := Fin p.2 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (ℤ → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => visibleCylinder p.1 p.2 w) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H),
    HasOriginalCylinders (jointLaw θ : Measure (PathSpace H)) θ ∧
    HasOriginalCylinders (retainedLaw θ : Measure (PathSpace (Positive θ))) (trim θ) ∧
    (retainedLaw θ : Measure (PathSpace (Positive θ))).map (includePath θ) = jointLaw θ ∧
    (retainedLaw θ : Measure (PathSpace (Positive θ))).map Prod.snd = visibleLaw θ ∧
    (∀ a : ℤ, (retainedLaw θ : Measure (PathSpace (Positive θ))).map (shift a) = retainedLaw θ) ∧
    (∀ a : ℤ, (jointLaw θ : Measure (PathSpace H)).map (shift a) = jointLaw θ) ∧
    (∀ a : ℤ, (visibleLaw θ : Measure (ℤ → Bool)).map (fun z t => z (a + t)) =
      visibleLaw θ) ∧
    (∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool),
      (visibleLaw θ : Measure (ℤ → Bool)).real (R.readout () ⟨t,n⟩ w) =
        ∑ i, θ.initial i * futureMass θ.matrix i n w) ∧
    (∀ᵐ z ∂(visibleLaw θ : Measure (ℤ → Bool)),
      ∀ t : ℤ, ¬(z t = true ∧ z (t + 1) = true)) ∧
    ((trim θ).matrix true * (trim θ).matrix true = 0) ∧
    (∀ (hu : RowUnifilar (trim θ).matrix) (t : ℤ) (n : ℕ)
      (w : Fin n → Bool) (a : FutureClass (trim θ).matrix),
      (jointLaw θ : Measure (PathSpace H)).real (retainedEndpoint θ t n w a) =
        ∑ i : Positive θ, (trim θ).initial i *
          if endpoint (quotientSuccessor (trim θ).matrix) n (classOf (trim θ).matrix i) w = a
          then wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix)
            n (classOf (trim θ).matrix i) w else 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  rcases h MarkedPredictiveQuotient.toy.{u} with ⟨_,_,_,_,_,_,_,hm,_⟩
  have hh := hm 0 0 (fun i => nomatch i)
  simpa [rejected,realize,MarkedPredictiveQuotient.toy,futureMass,wordMatrix] using hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨0,1⟩,(fun _ => false),(fun _ => true),?_⟩
  intro h
  have hz : (fun _ : ℤ => false) ∈ visibleCylinder 0 1 (fun _ => false) := by
    intro k
    rfl
  change visibleCylinder 0 1 (fun _ => false) = visibleCylinder 0 1 (fun _ => true) at h
  rw [h] at hz
  exact Bool.noConfusion (hz 0)

def family : Registration arena.{u} (type_of% (@same_law_trimming.{u})) where
  actual := realize signature (fun _ p w => visibleCylinder p.1 p.2 w) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@same_law_trimming.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@same_law_trimming.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p w => visibleCylinder p.1 p.2 w) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
    definition := none
    coordinates := #[5,6]
    readouts := #[{
      path := #["body","body","body","body","body","arg","arg","arg","arg","arg","arg","arg","fn","arg","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
