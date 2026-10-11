import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativePeriodicWordLaw FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeFullResidual
open NativeObserverJointLaw NativeInstalledFullLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory
open scoped ENNReal

private def heterogeneous : Parameters :=
  ⟨1/4,fun i => if i = 0 then 1/3 else 2/5,fun _ => 1/3,
    by norm_num,by norm_num,
    fun i => by split_ifs <;> norm_num,fun _ => by norm_num⟩

abbrev wordSignature : Signature where
  Params := (_ : Parameters) × ActivePhase
  State _ := Config
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure RawTail
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ p z => wordLaw p.1 p.2 z) (fun e => nomatch e)
def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ _ => 0) (fun e => nomatch e)

def identificationArena : Arena where
  signature := wordSignature
  Law R := ∀ (T : Parameters) (s : ActivePhase) (z : Config),
    z.1.control = .fourth (.active s) →
    (∀ n b, (R.readout () ⟨T,s⟩ z).real {some (typeWord s n b)} = sourceCoord T s n b z.2) ∧
      (s = .beta → (R.readout () ⟨T,s⟩ z).real {some [1]} = 1-T.v z.2)

def normalizationArena : Arena where
  signature := wordSignature
  Law R := ∀ (T : Parameters) (s : ActivePhase) (z : Config),
    z.1.control = .fourth (.active s) →
    R.readout () ⟨T,s⟩ z Set.univ = 1 ∧ R.readout () ⟨T,s⟩ z {none} = 0

private theorem word_dependence : ObservationalDependence wordSignature wordActual := by
  intro role
  refine ⟨⟨heterogeneous,.p⟩,atLabel .p 0,atLabel .p 1,?_⟩
  intro he
  have hm := congrArg (fun μ : Measure RawTail => μ.real {some (typeWord .p 0 0)}) he
  change (wordLaw heterogeneous .p (atLabel .p 0)).real {some (typeWord .p 0 0)} =
    (wordLaw heterogeneous .p (atLabel .p 1)).real {some (typeWord .p 0 0)} at hm
  rw [(native_word_identification heterogeneous .p _ rfl).1,
    (native_word_identification heterogeneous .p _ rfl).1] at hm
  norm_num [sourceCoord,heterogeneous,atLabel] at hm

private theorem rejected_identification : ¬ identificationArena.Law wordRejected := by
  intro law
  have hm := (law heterogeneous .p (atLabel .p 0) rfl).1 0 0
  norm_num [wordRejected,realize,sourceCoord,heterogeneous,atLabel,Measure.real] at hm

private theorem rejected_normalization : ¬ normalizationArena.Law wordRejected := by
  intro law
  have hm := (law heterogeneous .p (atLabel .p 0) rfl).1
  change (0 : Measure RawTail) Set.univ = 1 at hm
  simpa using hm

def identificationRecord : Registration identificationArena (type_of% (@native_word_identification)) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨native_word_identification,wordRejected,rejected_identification⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected,?_,rfl,rejected_identification⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := word_dependence

def normalizationRecord : Registration normalizationArena (type_of% (@native_noncompletion)) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨native_noncompletion,wordRejected,rejected_normalization⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected,?_,rfl,rejected_normalization⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := word_dependence

abbrev fullSignature : Signature where
  Params := Parameters
  State _ := Config
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure FullTranscript
  Anchor := Empty
  finiteAnchor := inferInstance

def fullActual : Realization fullSignature :=
  realize fullSignature (fun _ T z => fullLaw (observer T) (emitter T) z)
    (fun e => nomatch e)
def fullRejected : Realization fullSignature :=
  realize fullSignature (fun _ _ _ => 0) (fun e => nomatch e)

def observedBoxes (R : Realization fullSignature) (T : Parameters) : Prop :=
  ∀ (c : AcquiredNativeState) (s : ActivePhase),
    c.source.finiteFields.control = .fourth (.active s) → ∀ (i : Label) (t : ValidTail s),
      InBox ((R.readout () T (c.source.finiteFields,i)).real {fullRenderer c s t})
        ((endpointFull ConstantSuspensionSeparator.endpointA c).real {fullRenderer c s t})
        ((endpointFull ConstantSuspensionSeparator.endpointB c).real {fullRenderer c s t})

def criterionArena : Arena where
  signature := fullSignature
  Law R := ∀ T : Parameters,
    (observedBoxes R T ↔ Rates T ∧ ImmediateBoxes T ∧ Seeds T) ∧
      (∀ (c : AcquiredNativeState) (s : ActivePhase),
        c.source.finiteFields.control = .fourth (.active s) → ∀ i : Label,
          R.readout () T (c.source.finiteFields,i) Set.univ = 1 ∧
            R.readout () T (c.source.finiteFields,i) {fullRenderer c s ⟨none,trivial⟩} = 0)

private def delivered : FiniteFields :=
  { initial.source.finiteFields with control := .fourth .delivered }
private def secondDelivered : FiniteFields :=
  { delivered with registers := { delivered.registers with seed := some 0 } }

private theorem full_dependence : ObservationalDependence fullSignature fullActual := by
  intro role
  refine ⟨heterogeneous,(delivered,0),(secondDelivered,0),?_⟩
  intro he
  have h1 := (installed_full_law (observer heterogeneous) (emitter heterogeneous)).2.2.2.2.1
    (delivered,0) rfl
  have h2 := (installed_full_law (observer heterogeneous) (emitter heterogeneous)).2.2.2.2.1
    (secondDelivered,0) rfl
  change fullLaw (observer heterogeneous) (emitter heterogeneous) (delivered,0) =
    fullLaw (observer heterogeneous) (emitter heterogeneous) (secondDelivered,0) at he
  rw [h1,h2] at he
  have ht : terminalTranscript delivered = terminalTranscript secondDelivered := injective_dirac he
  have hf := congrFun ht 0
  have hs : delivered.registers.seed = secondDelivered.registers.seed :=
    congrArg (fun f : FiniteFields => f.registers.seed) (by simpa [terminalTranscript] using hf)
  change (none : Option Letter) = some 0 at hs
  cases hs

private theorem rejected_criterion : ¬ criterionArena.Law fullRejected := by
  intro law
  have hm := (law heterogeneous).2 (representative (atLabel .p 0).1) .p rfl 0 |>.1
  change (0 : Measure FullTranscript) Set.univ = 1 at hm
  simpa using hm

def criterionRecord : Registration criterionArena (type_of% (@native_full_box_criterion)) where
  actual := fullActual
  bridge := Iff.rfl
  variation := ⟨native_full_box_criterion,fullRejected,rejected_criterion⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fullRejected,?_,rfl,rejected_criterion⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := full_dependence


def identificationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_word_identification) (type_of% (realize wordSignature (fun _ p z => wordLaw p.1 p.2 z) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.identification,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.identificationRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨identificationArena⟩, objectArena := .source ⟨identificationArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source identificationArena ⟨identificationRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize wordSignature (fun _ p z => wordLaw p.1 p.2 z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw,
    definition := none, coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms identificationRecord


def normalizationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_noncompletion) (type_of% (realize wordSignature (fun _ p z => wordLaw p.1 p.2 z) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.normalization,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.normalizationRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨normalizationArena⟩, objectArena := .source ⟨normalizationArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source normalizationArena ⟨normalizationRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize wordSignature (fun _ p z => wordLaw p.1 p.2 z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw,
    definition := none, coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms normalizationRecord


def criterionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_full_box_criterion) (type_of% (realize fullSignature (fun _ T z => fullLaw (observer T) (emitter T) z) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.criterion,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw.criterionRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨criterionArena⟩, objectArena := .source ⟨criterionArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source criterionArena ⟨criterionRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize fullSignature (fun _ T z => fullLaw (observer T) (emitter T) z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw,
    definition := none, coordinates := #[0], readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "body", "body", "body", "body", "body", "fn", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms criterionRecord

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw
