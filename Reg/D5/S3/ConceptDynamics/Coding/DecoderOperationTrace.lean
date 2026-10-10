import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

universe u v w
noncomputable section

abbrev Params : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Σ O : Type w, Σ _ : C → Op C I O, ℕ → Option I

abbrev relationSignature : Signature where
  Params := Params.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev traceSignature : Signature where
  Params := Params.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → List p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def stepActual : Realization relationSignature.{u,v,w} :=
  realize relationSignature (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e)

def traceActual : Realization traceSignature.{u,v,w} :=
  realize traceSignature (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e)

def runActual : Realization relationSignature.{u,v,w} :=
  realize relationSignature (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e)

def stepRejected : Realization relationSignature.{u,v,w} :=
  realize relationSignature (fun _ _ _ _ => True) (fun (e : Empty) _ => Empty.elim e)

def traceRejected : Realization traceSignature.{u,v,w} :=
  realize traceSignature (fun _ _ _ _ _ => True) (fun (e : Empty) _ => Empty.elim e)

def runRejected : Realization relationSignature.{u,v,w} :=
  realize relationSignature (fun _ _ _ _ => False) (fun (e : Empty) _ => Empty.elim e)

abbrev stepArena : Arena where
  signature := relationSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (input : ℕ → Option I),
    Relator.RightUnique (R.readout () ⟨C, I, O, action, input⟩)

abbrev traceArena : Arena where
  signature := traceSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} {vertices : List C}
    (_h : R.readout () ⟨C, I, O, action, input⟩ s t vertices),
    Relation.ReflTransGen (Step action input) s t

abbrev runClosureArena : Arena where
  signature := relationSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {input : ℕ → Option I} {s t : Frame C O},
    R.readout () ⟨C, I, O, action, input⟩ s t ↔
      Relation.ReflTransGen (Step action input) s t

abbrev runTransArena : Arena where
  signature := relationSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {input : ℕ → Option I} {s t z : Frame C O}
    (_h : Run action input s t) (_g : Run action input t z),
    R.readout () ⟨C, I, O, action, input⟩ s z

abbrev runComparableArena : Arena where
  signature := relationSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {input : ℕ → Option I} {s t z : Frame C O}
    (_h : Run action input s t) (_g : Run action input s z),
    R.readout () ⟨C, I, O, action, input⟩ t z ∨ Run action input z t

/-- These inhabited fibers witness global variation; the Laws quantify over all fibers. -/
private def sampleFrame (n : ℕ) : Frame (ULift.{u} Unit) (ULift.{w} Unit) :=
  ⟨⟨()⟩, n, []⟩

private def idleAction : ULift.{u} Unit →
    Op (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) :=
  fun c => .internal c []

private def sampleParams : Params.{u,v,w} :=
  ⟨ULift.{u} Unit, ULift.{v} Unit, ULift.{w} Unit, idleAction, fun _ => none⟩

private theorem no_run_back
    (action : ULift.{u} Unit → Op (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit))
    (input : ℕ → Option (ULift.{v} Unit)) :
    ¬ Run action input (sampleFrame 1) (sampleFrame 0) := by
  intro h
  have bound := (run_mono h).1
  change 1 ≤ 0 at bound
  omega

theorem step_rejected_law : ¬ stepArena.{u,v,w}.Law stepRejected.{u,v,w} := by
  intro h
  have unique := h idleAction.{u,v,w} (fun _ => none)
  have equal : sampleFrame.{u,w} 0 = sampleFrame.{u,w} 1 :=
    unique (a := sampleFrame 0) True.intro True.intro
  have impossible : (0 : ℕ) = 1 := congrArg Frame.acquired equal
  omega

theorem trace_rejected_law : ¬ traceArena.{u,v,w}.Law traceRejected.{u,v,w} := by
  intro h
  have closure := h (action := idleAction.{u,v,w}) (input := fun _ => none)
    (s := sampleFrame 1) (t := sampleFrame 0) (vertices := []) True.intro
  exact no_run_back _ _ (run_closure.mpr closure)

theorem run_closure_rejected_law : ¬ runClosureArena.{u,v,w}.Law runRejected.{u,v,w} := by
  intro h
  exact (h (action := idleAction.{u,v,w}) (input := fun _ => none)
    (s := sampleFrame 0) (t := sampleFrame 0)).mpr .refl

theorem run_trans_rejected_law : ¬ runTransArena.{u,v,w}.Law runRejected.{u,v,w} := by
  intro h
  exact h (action := idleAction.{u,v,w}) (input := fun _ => none)
    (s := sampleFrame 0) (t := sampleFrame 0) (z := sampleFrame 0)
    ⟨_, .refl⟩ ⟨_, .refl⟩

theorem run_comparable_rejected_law : ¬ runComparableArena.{u,v,w}.Law runRejected.{u,v,w} := by
  intro h
  let action : ULift.{u} Unit →
      Op (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) :=
    fun _ => .acquire (fun _ => some (⟨()⟩, []))
  let input : ℕ → Option (ULift.{v} Unit) := fun _ => some ⟨()⟩
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

theorem run_dependence : ObservationalDependence relationSignature.{u,v,w} runActual.{u,v,w} := by
  intro i
  refine ⟨sampleParams, sampleFrame 0, sampleFrame 1, ?_⟩
  intro h
  have equal : Run idleAction.{u,v,w} (fun _ => none) (sampleFrame 0) (sampleFrame 0) =
      Run idleAction.{u,v,w} (fun _ => none) (sampleFrame 1) (sampleFrame 0) :=
    congrFun h (sampleFrame 0)
  exact no_run_back _ _ (equal.mp ⟨_, Trace.refl⟩)

def stepRegistration : Registration stepArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique.{u,v,w})) where
  actual := stepActual
  bridge := Iff.rfl
  variation := ⟨@step_unique.{u,v,w}, stepRejected, step_rejected_law⟩
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
    have edge : Step idleAction.{u,v,w} (fun _ => none) (sampleFrame 0) (sampleFrame 0) :=
      Step.internal (action := idleAction.{u,v,w}) (input := fun _ => none)
        ⟨()⟩ ⟨()⟩ 0 [] [] rfl
    have equal : Step idleAction.{u,v,w} (fun _ => none) (sampleFrame 0) (sampleFrame 0) =
        Step idleAction.{u,v,w} (fun _ => none) (sampleFrame 1) (sampleFrame 0) :=
      congrFun h (sampleFrame 0)
    exact no_run_back _ _ ⟨_, Trace.refl.tail (equal.mp edge)⟩

def traceRegistration : Registration traceArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure.{u,v,w})) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@trace_closure.{u,v,w}, traceRejected, trace_rejected_law⟩
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
    have equal : Trace idleAction.{u,v,w} (fun _ => none) (sampleFrame 0) (sampleFrame 0) [⟨()⟩] =
        Trace idleAction.{u,v,w} (fun _ => none) (sampleFrame 1) (sampleFrame 0) [⟨()⟩] :=
      congrFun (congrFun h (sampleFrame 0)) [⟨()⟩]
    exact no_run_back _ _ ⟨_, equal.mp Trace.refl⟩

def runClosureRegistration : Registration runClosureArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure.{u,v,w})) where
  actual := runActual
  bridge := Iff.rfl
  variation := ⟨@run_closure.{u,v,w}, runRejected, run_closure_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_closure_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def runTransRegistration : Registration runTransArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans.{u,v,w})) where
  actual := runActual
  bridge := Iff.rfl
  variation := ⟨@run_trans.{u,v,w}, runRejected, run_trans_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runRejected, ?_, rfl, run_trans_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def runComparableRegistration : Registration runComparableArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable.{u,v,w})) where
  actual := runActual
  bridge := Iff.rfl
  variation := ⟨@run_comparable.{u,v,w}, runRejected, run_comparable_rejected_law⟩
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
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique.{u,v,w})
      (type_of% (realize relationSignature.{u,v,w}
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
  readout := some stepActual
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
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure.{u,v,w})
      (type_of% (realize traceSignature.{u,v,w}
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
  readout := some traceActual
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
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure.{u,v,w})
      (type_of% (realize relationSignature.{u,v,w}
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
  readout := some runActual
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
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans.{u,v,w})
      (type_of% (realize relationSignature.{u,v,w}
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
  readout := some runActual
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
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable.{u,v,w})
      (type_of% (realize relationSignature.{u,v,w}
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
  readout := some runActual
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
