import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory LeanInformationAudit
open scoped BigOperators Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
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
    (θ : Presentation H) (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (_hc : HasOriginalCylinders J θ) (t : ℤ) (n : ℕ) (w : Fin n → Bool),
    (J.map Prod.snd).real (R.readout () ⟨t,n⟩ w) =
      ∑ i, θ.initial i * futureMass θ.matrix i n w

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let θ := MarkedPredictiveQuotient.toy.{u}
  obtain ⟨J,hc,_⟩ := original_law θ
  have hh := h θ (J : Measure _) hc 0 0 (fun i => nomatch i)
  simpa [rejected,realize,θ,MarkedPredictiveQuotient.toy,futureMass,wordMatrix] using hh

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

def family : Registration arena.{u} (type_of% (@visible_masses.{u})) where
  actual := realize signature (fun _ p w => visibleCylinder p.1 p.2 w) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@visible_masses.{u},rejected,rejected_law⟩
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
    (@visible_masses.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw.family
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
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
    definition := none
    coordinates := #[8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]


@[reducible] def existenceArena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H), ∃ J : ProbabilityMeasure (PathSpace H),
      HasOriginalCylinders (J : Measure (PathSpace H)) θ ∧
      (∀ a : ℤ, (J : Measure (PathSpace H)).map (shift a) = J) ∧
      (∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool),
        ((J : Measure (PathSpace H)).map Prod.snd).real (R.readout () ⟨t,n⟩ w) =
          ∑ i, θ.initial i * futureMass θ.matrix i n w) ∧
      (∀ᵐ z ∂((J : Measure (PathSpace H)).map Prod.snd),
        ∀ t : ℤ, ¬(z t = true ∧ z (t + 1) = true))

private theorem existence_rejected : ¬ existenceArena.{u}.Law rejected := by
  intro h
  obtain ⟨J,_,_,hm,_⟩ := h MarkedPredictiveQuotient.toy.{u}
  have hh := hm 0 0 (fun i => nomatch i)
  simpa [rejected,realize,MarkedPredictiveQuotient.toy,futureMass,wordMatrix] using hh

def existenceFamily : Registration existenceArena.{u} (type_of% (@original_law.{u})) where
  actual := realize signature (fun _ p w => visibleCylinder p.1 p.2 w) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@original_law.{u},rejected,existence_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,existence_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

def existenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_law.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw.existenceUnit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw.existenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨existenceArena.{u}⟩
  objectArena := .source ⟨existenceArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source existenceArena.{u} ⟨existenceFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p w => visibleCylinder p.1 p.2 w) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
    definition := none
    coordinates := #[6,7]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","arg","fn","arg","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

@[reducible] def no11Signature : Signature where
  Params := Unit
  State _ := Measure (ℤ → Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter (ℤ → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def no11Actual : Realization no11Signature :=
  realize no11Signature (fun _ _ μ => ae μ) Empty.elim

def no11Rejected : Realization no11Signature :=
  realize no11Signature (fun _ _ _ => ⊤) Empty.elim

@[reducible] def no11Arena : Arena where
  signature := no11Signature
  Law R := ∀ {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (_hc : HasOriginalCylinders J θ),
    ∀ᶠ z in R.readout () () (J.map Prod.snd), ∀ t : ℤ,
      ¬(z t = true ∧ z (t + 1) = true)

private theorem no11_rejected : ¬ no11Arena.{u}.Law no11Rejected := by
  intro h
  obtain ⟨J,hc,_⟩ := original_law MarkedPredictiveQuotient.toy.{u}
  have hh := h MarkedPredictiveQuotient.toy (J : Measure _) hc
  change ∀ᶠ z in (⊤ : Filter (ℤ → Bool)), ∀ t : ℤ,
    ¬(z t = true ∧ z (t+1) = true) at hh
  exact (Filter.eventually_top.mp hh (fun _ => true) 0) ⟨rfl,rfl⟩

def no11Family : Registration no11Arena.{u} (type_of% (@visible_no11.{u})) where
  actual := realize no11Signature (fun _ _ μ => ae μ) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@visible_no11.{u},no11Rejected,no11_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨no11Rejected,?_,rfl,no11_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro _
    refine ⟨(),0,Measure.dirac (fun _ : ℤ => false),?_⟩
    intro he
    change ae (0 : Measure (ℤ → Bool)) = ae (Measure.dirac (fun _ : ℤ => false)) at he
    have hz : ∀ᵐ _z ∂(Measure.dirac (fun _ : ℤ => false)), False := by
      change Filter.Eventually _ (ae (Measure.dirac (fun _ : ℤ => false)))
      rw [← he, ae_zero]
      exact Filter.eventually_bot
    exact (ae_dirac_iff (by simp)).mp hz

def no11Audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@visible_no11.{u}) (Realization no11Signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw.no11Unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw.no11Family
  realizationSource := none
  generated := false
  arena := .source ⟨no11Arena.{u}⟩
  objectArena := .source ⟨no11Arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source no11Arena.{u} ⟨no11Family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize no11Signature (fun _ _ μ => ae μ) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
#print axioms existenceFamily
#print axioms existenceAudit
#print axioms no11Family
#print axioms no11Audit
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
