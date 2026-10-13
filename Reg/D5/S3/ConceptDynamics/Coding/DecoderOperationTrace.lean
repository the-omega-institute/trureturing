import Reg.Support.DecoderOperationTraceCohort
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

universe u_1 u_2 u_3
noncomputable section

abbrev Params : Type (max (u_1 + 1) (max (u_2 + 1) (u_3 + 1))) :=
  Σ C : Type u_1, Σ I : Type u_2, Σ O : Type u_3, Σ _ : C → Op C I O, ℕ → Option I

abbrev relationSignature : Signature where
  Params := Params.{u_1,u_2,u_3}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev traceSignature : Signature where
  Params := Params.{u_1,u_2,u_3}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → List p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def runActual : Realization relationSignature.{u_1,u_2,u_3} :=
  realize relationSignature (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e)

def stepRejected : Realization relationSignature.{u_1,u_2,u_3} :=
  realize relationSignature (fun _ _ _ _ => True) (fun (e : Empty) _ => Empty.elim e)

def traceRejected : Realization traceSignature.{u_1,u_2,u_3} :=
  realize traceSignature (fun _ _ _ _ _ => True) (fun (e : Empty) _ => Empty.elim e)

def runRejected : Realization relationSignature.{u_1,u_2,u_3} :=
  realize relationSignature (fun _ _ _ _ => False) (fun (e : Empty) _ => Empty.elim e)

abbrev stepArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    (action : C → Op C I O) (input : ℕ → Option I),
    Relator.RightUnique (R.readout () ⟨C, I, O, action, input⟩)

abbrev traceArena : Arena where
  signature := traceSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} {vertices : List C}
    (_h : R.readout () ⟨C, I, O, action, input⟩ s t vertices),
    Relation.ReflTransGen (Step action input) s t

abbrev runClosureArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I} {s t : Frame C O},
    R.readout () ⟨C, I, O, action, input⟩ s t ↔
      Relation.ReflTransGen (Step action input) s t

abbrev runTransArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I} {s t z : Frame C O}
    (_h : Run action input s t) (_g : Run action input t z),
    R.readout () ⟨C, I, O, action, input⟩ s z

abbrev runComparableArena : Arena where
  signature := relationSignature.{u_1,u_2,u_3}
  Law R := ∀ {C : Type u_1} {I : Type u_2} {O : Type u_3}
    {action : C → Op C I O} {input : ℕ → Option I} {s t z : Frame C O}
    (_h : Run action input s t) (_g : Run action input s z),
    R.readout () ⟨C, I, O, action, input⟩ t z ∨ Run action input z t

/-- These inhabited fibers witness global variation; the Laws quantify over all fibers. -/
private def sampleFrame (n : ℕ) : Frame (ULift.{u_1} Unit) (ULift.{u_3} Unit) :=
  ⟨⟨()⟩, n, []⟩

private def idleAction : ULift.{u_1} Unit →
    Op (ULift.{u_1} Unit) (ULift.{u_2} Unit) (ULift.{u_3} Unit) :=
  fun c => .internal c []

private def sampleParams : Params.{u_1,u_2,u_3} :=
  ⟨ULift.{u_1} Unit, ULift.{u_2} Unit, ULift.{u_3} Unit, idleAction, fun _ => none⟩

private theorem no_run_back
    (action : ULift.{u_1} Unit → Op (ULift.{u_1} Unit) (ULift.{u_2} Unit) (ULift.{u_3} Unit))
    (input : ℕ → Option (ULift.{u_2} Unit)) :
    ¬ Run action input (sampleFrame 1) (sampleFrame 0) := by
  intro h
  have bound := (run_mono h).1
  change 1 ≤ 0 at bound
  omega

theorem step_rejected_law : ¬ stepArena.{u_1,u_2,u_3}.Law stepRejected.{u_1,u_2,u_3} := by
  intro h
  have unique := h idleAction.{u_1,u_2,u_3} (fun _ => none)
  have equal : sampleFrame.{u_1,u_3} 0 = sampleFrame.{u_1,u_3} 1 :=
    unique (a := sampleFrame 0) True.intro True.intro
  have impossible : (0 : ℕ) = 1 := congrArg Frame.acquired equal
  omega

theorem trace_rejected_law : ¬ traceArena.{u_1,u_2,u_3}.Law traceRejected.{u_1,u_2,u_3} := by
  intro h
  have closure := h (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
    (s := sampleFrame 1) (t := sampleFrame 0) (vertices := []) True.intro
  exact no_run_back _ _ (run_closure.mpr closure)

theorem run_closure_rejected_law : ¬ runClosureArena.{u_1,u_2,u_3}.Law runRejected.{u_1,u_2,u_3} := by
  intro h
  exact (h (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
    (s := sampleFrame 0) (t := sampleFrame 0)).mpr .refl

theorem run_trans_rejected_law : ¬ runTransArena.{u_1,u_2,u_3}.Law runRejected.{u_1,u_2,u_3} := by
  intro h
  exact h (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
    (s := sampleFrame 0) (t := sampleFrame 0) (z := sampleFrame 0)
    ⟨_, .refl⟩ ⟨_, .refl⟩

theorem run_comparable_rejected_law : ¬ runComparableArena.{u_1,u_2,u_3}.Law runRejected.{u_1,u_2,u_3} := by
  intro h
  let action : ULift.{u_1} Unit →
      Op (ULift.{u_1} Unit) (ULift.{u_2} Unit) (ULift.{u_3} Unit) :=
    fun _ => .acquire (fun _ => some (⟨()⟩, []))
  let input : ℕ → Option (ULift.{u_2} Unit) := fun _ => some ⟨()⟩
  have edge : Step action input (sampleFrame 0) (sampleFrame 1) :=
    Step.acquire (action := action) (input := input)
      ⟨()⟩ ⟨()⟩ 0 [] [] (fun _ => some (⟨()⟩, [])) ⟨()⟩ rfl rfl rfl
  have forward : Run action input (sampleFrame 0) (sampleFrame 1) :=
    ⟨_, Trace.refl.tail edge⟩
  rcases h (action := action) (input := input)
      (s := sampleFrame 0) (t := sampleFrame 0) (z := sampleFrame 1)
      ⟨_, .refl⟩ forward with impossible | backward
  · exact impossible
  · exact no_run_back action input backward

theorem run_dependence : ObservationalDependence relationSignature.{u_1,u_2,u_3} runActual.{u_1,u_2,u_3} := by
  intro i
  refine ⟨sampleParams, sampleFrame 0, sampleFrame 1, ?_⟩
  intro h
  have equal : Run idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) =
      Run idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 1) (sampleFrame 0) :=
    congrFun h (sampleFrame 0)
  exact no_run_back _ _ (equal.mp ⟨_, Trace.refl⟩)

def stepRegistration : Registration stepArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@step_unique.{u_1,u_2,u_3}, stepRejected, step_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨stepRejected, ?_, rfl, step_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨sampleParams, sampleFrame 0, sampleFrame 1, ?_⟩
    intro h
    have edge : Step idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) :=
      Step.internal (action := idleAction.{u_1,u_2,u_3}) (input := fun _ => none)
        ⟨()⟩ ⟨()⟩ 0 [] [] rfl
    have equal : Step idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) =
        Step idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 1) (sampleFrame 0) :=
      congrFun h (sampleFrame 0)
    exact no_run_back _ _ ⟨_, Trace.refl.tail (equal.mp edge)⟩

def traceRegistration : Registration traceArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    traceSignature.{u_1,u_2,u_3}
    (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@trace_closure.{u_1,u_2,u_3}, traceRejected, trace_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨traceRejected, ?_, rfl, trace_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨sampleParams, sampleFrame 0, sampleFrame 1, ?_⟩
    intro h
    have equal : Trace idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 0) (sampleFrame 0) [⟨()⟩] =
        Trace idleAction.{u_1,u_2,u_3} (fun _ => none) (sampleFrame 1) (sampleFrame 0) [⟨()⟩] :=
      congrFun (congrFun h (sampleFrame 0)) [⟨()⟩]
    exact no_run_back _ _ ⟨_, equal.mp Trace.refl⟩

def runClosureRegistration : Registration runClosureArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@run_closure.{u_1,u_2,u_3}, runRejected, run_closure_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_closure_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def runTransRegistration : Registration runTransArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@run_trans.{u_1,u_2,u_3}, runRejected, run_trans_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_trans_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def runComparableRegistration : Registration runComparableArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable.{u_1,u_2,u_3})) where
  actual := (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  bridge := Iff.rfl
  variation := ⟨@run_comparable.{u_1,u_2,u_3}, runRejected, run_comparable_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_comparable_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def step_unique_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.stepRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨stepArena⟩
  objectArena := .source ⟨stepArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stepArena ⟨stepRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def trace_closure_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure.{u_1,u_2,u_3})
      (type_of% (realize traceSignature.{u_1,u_2,u_3}
        (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.traceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    traceSignature.{u_1,u_2,u_3}
    (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def run_closure_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.runClosureRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨runClosureArena⟩
  objectArena := .source ⟨runClosureArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runClosureArena ⟨runClosureRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def run_trans_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.runTransRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨runTransArena⟩
  objectArena := .source ⟨runTransArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runTransArena ⟨runTransRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def run_comparable_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.runComparableRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨runComparableArena⟩
  objectArena := .source ⟨runComparableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runComparableArena ⟨runComparableRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

universe u_1 u_2 u_3
noncomputable section

def run_mono_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_mono.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_mono_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.runMonoEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.runMonoArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.runMonoArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.runMonoArena.{u_1,u_2,u_3} ⟨Cohort.runMonoEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def trace_input_transfer_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_input_transfer.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.traceSignature.{u_1,u_2,u_3} Cohort.traceReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_input_transfer_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.traceInputTransferEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.traceInputTransferArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.traceInputTransferArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.traceInputTransferArena.{u_1,u_2,u_3} ⟨Cohort.traceInputTransferEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.traceSignature.{u_1,u_2,u_3} Cohort.traceReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def prefix_trace_iff_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.prefix_trace_iff.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.fullSignature.{u_1,u_2,u_3} Cohort.fullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.prefix_trace_iff_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.prefixTraceIffEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.prefixTraceIffArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.prefixTraceIffArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.prefixTraceIffArena.{u_1,u_2,u_3} ⟨Cohort.prefixTraceIffEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.fullSignature.{u_1,u_2,u_3} Cohort.fullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def drain_acquired_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_acquired.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.drainSignature.{u_1,u_2,u_3} Cohort.drainReadout.{u_1,u_2,u_3} Cohort.drainAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_acquired_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.drainAcquiredEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.drainAcquiredArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.drainAcquiredArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.drainAcquiredArena.{u_1,u_2,u_3} ⟨Cohort.drainAcquiredEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.drainSignature.{u_1,u_2,u_3} Cohort.drainReadout.{u_1,u_2,u_3} Cohort.drainAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def drain_run_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_run.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_run_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.drainRunEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.drainRunArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.drainRunArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.drainRunArena.{u_1,u_2,u_3} ⟨Cohort.drainRunEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def actual_cut_exists_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_cut_exists.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_2, 0, max u_1 u_3, 0}
        Cohort.cutSignature.{u_1,u_2,u_3} Cohort.cutReadout.{u_1,u_2,u_3} Cohort.cutAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_cut_exists_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.actualCutExistsEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.actualCutExistsArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.actualCutExistsArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.actualCutExistsArena.{u_1,u_2,u_3} ⟨Cohort.actualCutExistsEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_2, 0, max u_1 u_3, 0}
        Cohort.cutSignature.{u_1,u_2,u_3} Cohort.cutReadout.{u_1,u_2,u_3} Cohort.cutAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
