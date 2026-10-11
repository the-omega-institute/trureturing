import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw
open NativeObserverJointLaw NativeFullResidual NativeInstalledFullLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u
abbrev Complete := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.Complete
abbrev base := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.liftedBase

abbrev pathSignature : Signature where
  Params := Complete.{u}
  State C := ℕ → Marked C.Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := FullTranscript
  Anchor := Empty
  finiteAnchor := inferInstance

def pathActual : Realization pathSignature :=
  realize pathSignature (fun _ C x => markedTranscript C.observer x) (fun e => nomatch e)
def pathRejected : Realization pathSignature :=
  realize pathSignature (fun _ _ _ _ => none) (fun e => nomatch e)

def pathArena : Arena where
  signature := pathSignature
  Law R := ∀ (C : Complete.{u}) (x : ℕ → Marked C.Z),
    (∀ n, Edge C.observer (x n) (x (n+1))) →
    ∀ c : AcquiredNativeState, c.source.finiteFields = C.observer.project (x 0).1 →
    R.readout () C x = fullTranscript c (rawFrom x)

private def deliveredFields : FiniteFields :=
  { initial.source.finiteFields with control := .fourth .delivered }
private def deliveredPath : ℕ → Marked base.Z := fun _ => (ULift.up deliveredFields,none)

private theorem rejected_path : ¬ pathArena.{u}.Law pathRejected := by
  intro law
  have h := law base deliveredPath (fun _ => ⟨rfl,rfl⟩) (representative deliveredFields) rfl
  have hz := congrFun h 0
  change (none : FullOutput) = some ([],deliveredFields,[]) at hz
  cases hz

private theorem path_dependence : ObservationalDependence pathSignature.{u} pathActual := by
  intro i
  cases i
  refine ⟨base,(fun _ => (ULift.up initial.source.finiteFields,none)),deliveredPath,?_⟩
  intro h
  have hz := congrFun h 0
  have hf : initial.source.finiteFields = deliveredFields := by
    have hp := (show base.observer.project (ULift.up initial.source.finiteFields) =
        base.observer.project (ULift.up deliveredFields) ∧
        eventBlocks (base.observer.project (ULift.up initial.source.finiteFields)) [] =
          eventBlocks (base.observer.project (ULift.up deliveredFields)) [] from by
      simpa [pathActual,realize,markedTranscript,operations,deliveredPath] using hz).1
    exact hp
  have hc := congrArg FiniteFields.control hf
  exact NativeControl.noConfusion hc

def pathRecord : Registration pathArena.{u} (type_of% (@marked_native_realization.{u})) where
  actual := pathActual
  bridge := by
    constructor
    · intro T C x hx c hc
      exact T C.observer x hx c hc
    · intro T Z finite measurable singleton M x hx c hc
      exact T ⟨Z,finite,measurable,singleton,M⟩ x hx c hc
  variation := ⟨(fun C x hx c hc => marked_native_realization C.observer x hx c hc),
    pathRejected,rejected_path⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pathRejected,?_,rfl,rejected_path⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := path_dependence

def pathRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@marked_native_realization.{u})
    (type_of% (realize pathSignature.{u}
      (fun _ C x => markedTranscript C.observer x) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.path,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.pathRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨pathArena⟩, objectArena := .source ⟨pathArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source pathArena ⟨pathRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize pathSignature.{u}
    (fun _ C x => markedTranscript C.observer x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw,
    definition := none, coordinates := #[0,4], readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


private def emitted (f : FiniteFields) : Option Operation :=
  match f.control with
  | .fourth (.pending b) => some (.stop b)
  | .fourth .delivered => none
  | _ => some (.read 0)

def baseEmitter : InstalledEmitter base.observer where
  emit z := PMF.pure (emitted z.down)
  lawful := by
    intro z a ha
    have he := (PMF.mem_support_pure_iff _ _).mp ha
    subst a
    change match emitted z.down with
      | none => z.down.control = .fourth .delivered
      | some op => (finiteStep z.down op).isSome
    cases hc : z.down.control with
    | seed q => cases q <;> simp [emitted,hc,finiteStep,finiteRead]
    | early t q => simp [emitted,hc,finiteStep,finiteRead]
    | fourth q => cases q <;> simp [emitted,hc,finiteStep,finiteRead,finiteStop]

structure Installed where
  complete : Complete.{u}
  emitter : InstalledEmitter complete.observer

private def installedBase : Installed.{u} := ⟨base,baseEmitter⟩

local instance : Fintype base.Z := base.finite
local instance : MeasurableSpace base.Z := base.measurable
local instance : MeasurableSingletonClass base.Z := base.singletons

abbrev lawSignature : Signature where
  Params := Installed.{u}
  State C := C.complete.Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure FullTranscript
  Anchor := Empty
  finiteAnchor := inferInstance

def lawActual : Realization lawSignature :=
  realize lawSignature (fun _ C z => fullLaw C.complete.observer C.emitter z)
    (fun e => nomatch e)
def lawRejected : Realization lawSignature :=
  realize lawSignature (fun _ _ _ => 0) (fun e => nomatch e)

private def secondDelivered : FiniteFields :=
  { deliveredFields with registers := { deliveredFields.registers with seed := some 0 } }

private theorem law_dependence : ObservationalDependence lawSignature.{u} lawActual := by
  intro i
  cases i
  refine ⟨installedBase,ULift.up deliveredFields,ULift.up secondDelivered,?_⟩
  intro he
  have h1 := (installed_full_law base.observer baseEmitter).2.2.2.2.1
    (ULift.up deliveredFields) rfl
  have h2 := (installed_full_law base.observer baseEmitter).2.2.2.2.1
    (ULift.up secondDelivered) rfl
  change fullLaw base.observer baseEmitter (ULift.up deliveredFields) =
    fullLaw base.observer baseEmitter (ULift.up secondDelivered) at he
  rw [h1,h2] at he
  have ht : terminalTranscript deliveredFields = terminalTranscript secondDelivered :=
    injective_dirac he
  have hf := congrFun ht 0
  have hs : deliveredFields.registers.seed = secondDelivered.registers.seed :=
    congrArg (fun f : FiniteFields => f.registers.seed) (by simpa [terminalTranscript] using hf)
  change (none : Option Letter) = some 0 at hs
  cases hs

def identityArena : Arena where
  signature := lawSignature
  Law R := ∀ (C : Installed.{u}) (s : ActivePhase) (z : C.complete.Z)
    (c : AcquiredNativeState), C.complete.observer.project z = c.source.finiteFields →
    c.source.finiteFields.control = .fourth (.active s) →
    R.readout () C z = (tailLaw C.complete.observer C.emitter s z).map (fullRenderer c s)

private def activeFields : FiniteFields :=
  { initial.source.finiteFields with control := .fourth (.active .p) }

private theorem rejected_identity : ¬ identityArena.{u}.Law lawRejected := by
  intro h
  have he := h installedBase .p (ULift.up activeFields) (representative activeFields) rfl rfl
  have hm := congrArg (fun μ : Measure FullTranscript => μ Set.univ) he
  simp only [lawRejected,realize,Measure.coe_zero] at hm
  letI := instIsProbabilityMeasureValidTailTailLaw base.observer baseEmitter .p
    (ULift.up activeFields)
  have hp : IsProbabilityMeasure
      ((tailLaw base.observer baseEmitter .p (ULift.up activeFields)).map
        (fullRenderer (representative activeFields) .p)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  change (0 : ℝ≥0∞) =
    ((tailLaw base.observer baseEmitter .p (ULift.up activeFields)).map
      (fullRenderer (representative activeFields) .p)) Set.univ at hm
  exact zero_ne_one (hm.trans hp.measure_univ)

def identityRecord : Registration identityArena.{u}
    (type_of% (@installed_configuration_identity.{u})) where
  actual := lawActual
  bridge := by
    constructor
    · intro T C s z c hc hs; exact T C.complete.observer C.emitter s z c hc hs
    · intro T Z finite measurable singleton M e s z c hc hs
      exact T ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩ s z c hc hs
  variation := ⟨(fun C s z c hc hs => installed_configuration_identity
    C.complete.observer C.emitter s z c hc hs),lawRejected,rejected_identity⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lawRejected,?_,rfl,rejected_identity⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := law_dependence

def recursionArena : Arena where
  signature := lawSignature
  Law R := ∀ (C : Installed.{u}) (z : C.complete.Z) (op : Operation) (f' : FiniteFields),
    finiteStep (C.complete.observer.project z) op = some f' →
    ∀ E : Set FullTranscript, MeasurableSet E →
    R.readout () C z (blockEvent (C.complete.observer.project z) f' op E) =
      C.emitter.emit z (some op) * ∑ z' : C.complete.Z,
        C.complete.observer.update op z z' * fullLaw C.complete.observer C.emitter z' E

private theorem rejected_recursion : ¬ recursionArena.{u}.Law lawRejected := by
  intro h
  let f := initial.source.finiteFields
  let f' : FiniteFields := { f with control := .seed (some 0) }
  have hf : finiteStep f (.read 0) = some f' := rfl
  have he := h installedBase (ULift.up f) (.read 0) f' hf Set.univ MeasurableSet.univ
  change 0 = baseEmitter.emit (ULift.up f) (some (.read 0)) *
    ∑ z', base.observer.update (.read 0) (ULift.up f) z' *
      fullLaw base.observer baseEmitter z' Set.univ at he
  have hs : ∑ z', base.observer.update (.read 0) (ULift.up f) z' = 1 := by
    simpa only [tsum_fintype] using (base.observer.update (.read 0) (ULift.up f)).tsum_coe
  simp only [measure_univ,mul_one,hs] at he
  have hm : baseEmitter.{u}.emit (ULift.up f) (some (.read 0)) = 1 := PMF.pure_apply_self _
  rw [hm,one_mul] at he
  exact zero_ne_one (he.trans hs)

def recursionRecord : Registration recursionArena.{u}
    (type_of% (@installed_first_block_recursion.{u})) where
  actual := lawActual
  bridge := by
    constructor
    · intro T C z op f' hf E hE; exact T C.complete.observer C.emitter z op f' hf E hE
    · intro T Z finite measurable singleton M e z op f' hf E hE
      exact T ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩ z op f' hf E hE
  variation := ⟨(fun C z op f' hf E hE => installed_first_block_recursion
    C.complete.observer C.emitter z op f' hf E hE),lawRejected,rejected_recursion⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lawRejected,?_,rfl,rejected_recursion⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := law_dependence

def fullArena : Arena where
  signature := lawSignature
  Law R := ∀ C : Installed.{u},
    (∀ z : C.complete.Z, IsProbabilityMeasure (R.readout () C z)) ∧
    (∀ z : C.complete.Z, ∀ᵐ x ∂markedLaw C.complete.observer C.emitter (z,none),
      markedTranscript C.complete.observer x =
        fullTranscript (representative (C.complete.observer.project z)) (rawFrom x)) ∧
    (∀ (z : C.complete.Z) (op : Operation) (f' : FiniteFields),
      finiteStep (C.complete.observer.project z) op = some f' →
      ∀ E : Set FullTranscript, MeasurableSet E →
      R.readout () C z (blockEvent (C.complete.observer.project z) f' op E) =
        C.emitter.emit z (some op) * ∑ z' : C.complete.Z,
          C.complete.observer.update op z z' * R.readout () C z' E) ∧
    (∀ (z : C.complete.Z) (b : Letter),
      (C.complete.observer.project z).control = .fourth (.pending b) →
      C.emitter.emit z = PMF.pure (some (.stop b))) ∧
    (∀ z : C.complete.Z, (C.complete.observer.project z).control = .fourth .delivered →
      R.readout () C z = Measure.dirac (terminalTranscript (C.complete.observer.project z))) ∧
    (∀ (μ : PMF Depth) (s : ActivePhase),
      installedRisk C.complete.observer C.emitter μ s =
        rawRisk C.complete.observer μ s (fun _ z => tailLaw C.complete.observer C.emitter s z))

private theorem rejected_full : ¬ fullArena.{u}.Law lawRejected := by
  intro h
  have hp := (h installedBase).1 (ULift.up deliveredFields)
  change IsProbabilityMeasure (0 : Measure FullTranscript) at hp
  have hm : (0 : Measure FullTranscript) Set.univ = 1 := hp.measure_univ
  exact zero_ne_one (by simpa only [Measure.coe_zero,Pi.zero_apply] using hm)

def fullRecord : Registration fullArena.{u} (type_of% (@installed_full_law.{u})) where
  actual := lawActual
  bridge := by
    constructor
    · intro T C; exact T C.complete.observer C.emitter
    · intro T Z finite measurable singleton M e
      exact T ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩
  variation := ⟨(fun C => installed_full_law C.complete.observer C.emitter),
    lawRejected,rejected_full⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lawRejected,?_,rfl,rejected_full⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := law_dependence

def identityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@installed_configuration_identity.{u})
    (type_of% (realize lawSignature.{u}
      (fun _ C z => fullLaw C.complete.observer C.emitter z) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.identity,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.identityRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨identityArena⟩, objectArena := .source ⟨identityArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source identityArena ⟨identityRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize lawSignature.{u}
    (fun _ C z => fullLaw C.complete.observer C.emitter z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw,
    definition := none, coordinates := #[0,4,5], readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def recursionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@installed_first_block_recursion.{u})
    (type_of% (realize lawSignature.{u}
      (fun _ C z => fullLaw C.complete.observer C.emitter z) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.recursion,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.recursionRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨recursionArena⟩, objectArena := .source ⟨recursionArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source recursionArena ⟨recursionRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize lawSignature.{u}
    (fun _ C z => fullLaw C.complete.observer C.emitter z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw,
    definition := none, coordinates := #[0,4,5], readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def fullRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@installed_full_law.{u})
    (type_of% (realize lawSignature.{u}
      (fun _ C z => fullLaw C.complete.observer C.emitter z) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.full,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.fullRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨fullArena⟩, objectArena := .source ⟨fullArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source fullArena ⟨fullRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize lawSignature.{u}
    (fun _ C z => fullLaw C.complete.observer C.emitter z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw,
    definition := none, coordinates := #[0,4,5], readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","body","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms pathRecord
#print axioms identityRecord
#print axioms recursionRecord
#print axioms fullRecord

namespace PeriodicReuse
noncomputable section
abbrev markedSignature : Signature where
  Params := Installed.{u}
  State C := Marked C.complete.Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := Measure (ℕ → Marked C.complete.Z)
  Anchor := Empty
  finiteAnchor := inferInstance

def markedActual : Realization markedSignature :=
  realize markedSignature (fun _ C w => markedLaw C.complete.observer C.emitter w)
    (fun e => nomatch e)
def regenerationRejected : Realization markedSignature :=
  realize markedSignature (fun _ _ _ => 0) (fun e => nomatch e)
def headRejected : Realization markedSignature :=
  realize markedSignature (fun _ C w => markedLaw C.complete.observer C.emitter
    (w.1,some (.read 0)))
    (fun e => nomatch e)
def regenerationArena : Arena where
  signature := markedSignature
  Law R := ∀ (C : Installed.{u}) (w : Marked C.complete.Z),
    R.readout () C w = ∑ v : Marked C.complete.Z,
      markedRow C.complete.observer C.emitter w v •
        (markedLaw C.complete.observer C.emitter v).map (fun x => prepend w x)
def headArena : Arena where
  signature := markedSignature
  Law R := ∀ (C : Installed.{u}) (w : Marked C.complete.Z),
    ∀ᵐ x ∂R.readout () C w, x 0 = w
private def wnone : Marked base.Z := (ULift.up initial.source.finiteFields,none)
private def wread : Marked base.Z := (ULift.up initial.source.finiteFields,some (.read 0))

private theorem marked_distinct (C : Installed.{u}) (z : C.complete.Z) :
    markedLaw C.complete.observer C.emitter (z,none) ≠
      markedLaw C.complete.observer C.emitter (z,some (.read 0)) := by
  intro he
  have h0 := marked_head C.complete.observer C.emitter (z,none)
  have h1 := marked_head C.complete.observer C.emitter (z,some (.read 0))
  rw [← he] at h1
  obtain ⟨x,hx0,hx1⟩ := (h0.and h1).exists
  have hm : (z,(none : Option Operation)) = (z,some (Operation.read 0)) := hx0.symm.trans hx1
  have hn := congrArg Prod.snd hm
  cases hn

private theorem marked_dependence : ObservationalDependence markedSignature.{u} markedActual := by
  intro role
  refine ⟨installedBase,wnone,wread,?_⟩
  exact marked_distinct installedBase (ULift.up initial.source.finiteFields)

private theorem rejected_regeneration : ¬ regenerationArena.{u}.Law regenerationRejected := by
  intro law
  have impossible (C : Installed.{u}) (w : Marked C.complete.Z) : False := by
    have he : (0 : Measure (ℕ → Marked C.complete.Z)) =
        markedLaw C.complete.observer C.emitter w :=
      (law C w).trans (marked_regenerate C.complete.observer C.emitter w).symm
    have hm := congrArg (fun μ : Measure (ℕ → Marked C.complete.Z) => μ Set.univ) he
    simp only [Measure.coe_zero,Pi.zero_apply,measure_univ] at hm
    exact zero_ne_one hm
  exact impossible installedBase wnone

private theorem rejected_head : ¬ headArena.{u}.Law headRejected := by
  intro law
  have impossible (C : Installed.{u}) (z : C.complete.Z) : False := by
    have he := law C (z,none)
    have hh := marked_head C.complete.observer C.emitter (z,some (.read 0))
    change ∀ᵐ x ∂markedLaw C.complete.observer C.emitter (z,some (.read 0)),
      x 0 = (z,none) at he
    obtain ⟨x,hx0,hx1⟩ := (he.and hh).exists
    have hm : (z,(none : Option Operation)) = (z,some (Operation.read 0)) := hx0.symm.trans hx1
    have hn := congrArg Prod.snd hm
    cases hn
  exact impossible installedBase (ULift.up initial.source.finiteFields)

def regenerationRecord : Registration regenerationArena.{u} (type_of% (@marked_regenerate.{u})) where
  actual := markedActual
  bridge := by
    constructor
    · intro T C w; exact T C.complete.observer C.emitter w
    · intro T Z finite measurable singleton M e w
      exact T ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩ w
  variation := ⟨(fun C w => marked_regenerate C.complete.observer C.emitter w),
    regenerationRejected,rejected_regeneration⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨regenerationRejected,?_,rfl,rejected_regeneration⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := marked_dependence

private theorem head_bridge : (type_of% (@marked_head.{u})) ↔ headArena.{u}.Law markedActual := by
  constructor
  · intro T C w; exact T C.complete.observer C.emitter w
  · intro T Z finite measurable singleton M e w
    exact T ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩ w
private theorem head_positive : headArena.{u}.Law markedActual :=
  fun C w => marked_head C.complete.observer C.emitter w
private theorem singleton_sensitivity (A : Arena) (actual bad : Realization A.signature)
    [Subsingleton A.signature.Role] [IsEmpty A.signature.Anchor] (hbad : ¬ A.Law bad) :
    Sensitivity A actual := by
  constructor
  · intro i
    refine ⟨bad,?_,?_,hbad⟩
    · intro j hj; exact False.elim (hj (Subsingleton.elim j i))
    · funext a; exact isEmptyElim a
  · intro a; exact isEmptyElim a
private theorem head_sensitivity : Sensitivity headArena.{u} markedActual := by
  letI : Subsingleton headArena.signature.Role := (inferInstance : Subsingleton Unit)
  letI : IsEmpty headArena.signature.Anchor := (inferInstance : IsEmpty Empty)
  exact singleton_sensitivity headArena markedActual headRejected rejected_head

def headRecord : Registration headArena.{u} (type_of% (@marked_head.{u})) where
  actual := markedActual
  bridge := head_bridge
  variation := ⟨head_positive,headRejected,rejected_head⟩
  sensitivity := head_sensitivity
  dependence := marked_dependence


def regenerationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@marked_regenerate.{u}) (type_of% (realize markedSignature.{u}
      (fun _ C w => markedLaw C.complete.observer C.emitter w) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.PeriodicReuse.regeneration,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.PeriodicReuse.regenerationRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨regenerationArena⟩, objectArena := .source ⟨regenerationArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source regenerationArena ⟨regenerationRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize markedSignature.{u}
    (fun _ C w => markedLaw C.complete.observer C.emitter w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw,
    definition := none, coordinates := #[0, 4, 5],
    readouts := #[{
        path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms regenerationRecord


def headRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@marked_head.{u}) (type_of% (realize markedSignature.{u}
      (fun _ C w => markedLaw C.complete.observer C.emitter w) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.PeriodicReuse.head,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.PeriodicReuse.headRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨headArena⟩, objectArena := .source ⟨headArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source headArena ⟨headRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize markedSignature.{u}
    (fun _ C w => markedLaw C.complete.observer C.emitter w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw,
    definition := none, coordinates := #[0, 4, 5],
    readouts := #[{
        path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms headRecord

end
end PeriodicReuse

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
