import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory LeanInformationAudit
open scoped BigOperators Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders

local notation "originalCylinder" => _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.cylinder

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
universe u

abbrev Parameters := Σ H : Type u, Σ _t : ℤ, Σ m : ℕ, Σ _n : ℕ,
  Σ _h : Fin (m + 1) → H, Fin m → Bool

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := Fin p.2.2.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (PathSpace p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p v =>
    originalCylinder (p.2.1-p.2.2.1) p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ∩
      Prod.snd ⁻¹' visibleCylinder p.2.1 p.2.2.2.1 v) Empty.elim

def rejected : Realization signature.{u} := realize signature (fun _ _ _ => ∅) Empty.elim

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (_hc : HasOriginalCylinders J θ) (t : ℤ) (m n : ℕ)
    (h : Fin (m+1) → H) (w : Fin m → Bool) (v : Fin n → Bool),
    J.real (R.readout () ⟨H,t,m,n,h,w⟩ v) = θ.initial (h 0) * pathMass θ.matrix m h w *
      futureMass θ.matrix (h (Fin.last m)) n v

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let θ := MarkedPredictiveQuotient.toy.{u}
  obtain ⟨J,hc,_⟩ := original_law θ
  have he := h θ (J : Measure _) hc 0 0 0 (fun _ => ⟨()⟩)
    (fun i => nomatch i) (fun i => nomatch i)
  simpa [rejected, realize, θ, MarkedPredictiveQuotient.toy, pathMass,
    futureMass, wordMatrix] using he

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  let p : Parameters.{u} := ⟨MarkedPredictiveQuotient.Toy,0,0,1,(fun _ => ⟨()⟩),(fun i => nomatch i)⟩
  refine ⟨p,(fun _ => false),(fun _ => true),?_⟩
  intro he
  have hm : MarkedPredictiveQuotient.toyPath.{u} ∈ actual.readout () p (fun _ => false) := by
    simp [actual,realize,p,MarkedPredictiveQuotient.toyPath,
      _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.cylinder,
      visibleCylinder]
  rw [he] at hm
  simpa [actual,realize,p,MarkedPredictiveQuotient.toyPath,
    _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.cylinder,
    visibleCylinder] using hm

def family : Registration arena.{u} (type_of% (@past_future_mass.{u})) where
  actual := realize signature (fun _ p v =>
    originalCylinder (p.2.1-p.2.2.1) p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ∩
      Prod.snd ⁻¹' visibleCylinder p.2.1 p.2.2.2.1 v) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@past_future_mass.{u},rejected,rejected_law⟩
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
    (@past_future_mass.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v =>
    originalCylinder (p.2.1-p.2.2.1) p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 ∩
      Prod.snd ⁻¹' visibleCylinder p.2.1 p.2.2.2.1 v) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
    definition := none
    coordinates := #[0,8,9,10,11,12]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","arg","arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
