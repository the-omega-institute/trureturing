import D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The complete kernel law retains its four coordinate-readout occurrences. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Reg.D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
open _root_.D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v

def signature : Signature where
  Params := Type v
  State X := X × X
  Role := Bool × Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinate (i : Bool) {X : Type v} (p : X × X) : X :=
  match i with
  | false => p.1
  | true => p.2

def FullLaw (r : Realization signature.{v}) : Prop :=
  ∀ {Z : Type u} {X : Type v} [MeasurableSpace Z] [MeasurableSpace X]
    [StandardBorelSpace X] (P Q : Kernel Z X) [IsMarkovKernel P] [IsMarkovKernel Q],
    IsMarkovKernel (maximalCoupling P Q) ∧
      (maximalCoupling P Q).map (show X × X → X from r.readout (false, false) X) = P ∧
      (maximalCoupling P Q).map (show X × X → X from r.readout (false, true) X) = Q ∧
      ∀ z, maximalCoupling P Q z
        {p | r.readout (true, false) X p ≠ r.readout (true, true) X p} =
          measurableTotalVariation (P z) (Q z)

def arena : Arena := ⟨signature.{v}, FullLaw.{u,v}⟩

def actual : Realization signature.{v} :=
  realize signature (fun i _ p => coordinate i.2 p) (fun e => nomatch e)

def changed (i : Bool × Bool) : Realization signature.{v} :=
  realize signature (fun (j : Bool × Bool) (_ : Type v) p =>
    coordinate (if j = i then !i.2 else j.2) p)
    (fun e => nomatch e)

abbrev TargetZ := ULift.{u} Unit
abbrev TargetX := ULift.{v} Bool

instance : DiscreteMeasurableSpace TargetX.{v} := ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass TargetX.{v} :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

instance : StandardBorelSpace TargetX.{v} :=
  standardBorelSpace_of_discreteMeasurableSpace

def targetP : Kernel TargetZ.{u} TargetX.{v} :=
  Kernel.deterministic (fun _ => ⟨false⟩) measurable_const

def targetQ : Kernel TargetZ.{u} TargetX.{v} :=
  Kernel.deterministic (fun _ => ⟨true⟩) measurable_const

instance : IsMarkovKernel targetP.{u,v} :=
  inferInstanceAs (IsMarkovKernel (Kernel.deterministic _ _))

instance : IsMarkovKernel targetQ.{u,v} :=
  inferInstanceAs (IsMarkovKernel (Kernel.deterministic _ _))

theorem targets_ne : targetP.{u,v} ≠ targetQ.{u,v} := by
  intro h
  have hmass := congrArg (fun K : Kernel TargetZ TargetX =>
    K ⟨()⟩ {⟨false⟩}) h
  simpa [targetP, targetQ, Kernel.deterministic_apply, Measure.dirac_apply] using hmass

theorem actual_law : FullLaw.{u,v} actual :=
  @maximal_coupling.{u,v}

theorem target_tv_ne_zero (z : TargetZ.{u}) :
    measurableTotalVariation (targetP.{u,v} z) (targetQ.{u,v} z) ≠ 0 := by
  intro h
  have e := le_iSup (fun E : {E : Set TargetX // MeasurableSet E} =>
    max (targetP z E.val - targetQ z E.val) (targetQ z E.val - targetP z E.val))
      ⟨{⟨false⟩}, measurableSet_singleton _⟩
  change _ ≤ measurableTotalVariation (targetP z) (targetQ z) at e
  rw [h] at e
  simpa [targetP, targetQ, Kernel.deterministic_apply, Measure.dirac_apply] using e

theorem changed_not_law (i : Bool × Bool) : ¬ FullLaw.{u,v} (changed i) := by
  intro h
  have hb := h targetP.{u,v} targetQ.{u,v}
  have ha := maximal_coupling targetP.{u,v} targetQ.{u,v}
  rcases i with ⟨group, axis⟩
  cases group <;> cases axis
  · have e : (maximalCoupling targetP targetQ).map Prod.snd = targetP := hb.2.1
    exact targets_ne (e.symm.trans ha.2.2.1)
  · have e : (maximalCoupling targetP targetQ).map Prod.fst = targetQ := hb.2.2.1
    exact targets_ne (ha.2.1.symm.trans e)
  · have e := hb.2.2.2 (ULift.up ())
    change (maximalCoupling targetP targetQ) _ {p | p.2 ≠ p.2} = _ at e
    rw [show {p : TargetX × TargetX | p.2 ≠ p.2} = ∅ by ext p; simp] at e
    have hz : (0 : ℝ≥0∞) = measurableTotalVariation
        (targetP (ULift.up ())) (targetQ (ULift.up ())) := by
      simpa using e
    exact target_tv_ne_zero _ hz.symm
  · have e := hb.2.2.2 (ULift.up ())
    change (maximalCoupling targetP targetQ) _ {p | p.1 ≠ p.1} = _ at e
    rw [show {p : TargetX × TargetX | p.1 ≠ p.1} = ∅ by ext p; simp] at e
    have hz : (0 : ℝ≥0∞) = measurableTotalVariation
        (targetP (ULift.up ())) (targetQ (ULift.up ())) := by
      simpa using e
    exact target_tv_ne_zero _ hz.symm

theorem variation : Variation arena.{u,v} actual :=
  ⟨actual_law, changed (false, false), changed_not_law (false, false)⟩

theorem sensitivity : Sensitivity arena.{u,v} actual := by
  classical
  constructor
  · intro i
    refine ⟨changed i, ?_, rfl, changed_not_law i⟩
    intro j hji
    funext X p
    dsimp only [actual, changed, realize]
    split_ifs with h
    · exact (hji h).elim
    · rfl
  · intro e
    exact nomatch e

theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  refine ⟨TargetX.{v}, (⟨false⟩, ⟨false⟩), (⟨true⟩, ⟨true⟩), ?_⟩
  rcases i with ⟨group, axis⟩
  cases axis <;> (change (ULift.up false : TargetX) ≠ ULift.up true)
  all_goals
    intro h
    have e := congrArg ULift.down h
    cases e

def registration : Registration arena.{u,v} (type_of% (@maximal_coupling.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,0,_,0,0}
    (@maximal_coupling.{u,v}) (Realization signature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling.maximalCouplingUnit
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i _ p => coordinate i.2 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 10, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 10, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Reg.D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
