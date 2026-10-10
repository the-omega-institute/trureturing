import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open FourthSegmentStoppedLaw FourthSegmentLawRecovery.Residual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory

abbrev eventSignature : Signature where
  Params := (_ : AcquiredNativeState) × ℕ
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := FullOutput
  Anchor := Empty
  finiteAnchor := inferInstance

def eventArena : Arena where
  signature := eventSignature
  Law R := ∀ (c d : AcquiredNativeState) (ω : Stream) (n k : ℕ)
    (ops : List Operation), nativeDrive c ω n = some (ops, d, k) →
    R.readout () ⟨c, n⟩ ω =
      some (ops, d.source.finiteFields, eventBlocks c.source.finiteFields ops) ∧
    (eventBlocks c.source.finiteFields ops).foldl replayBlock c.source.finiteFields =
      d.source.finiteFields ∧
    originalView ((eventBlocks c.source.finiteFields ops).foldl
      replayBlock c.source.finiteFields) = originalView d.source.finiteFields

def eventActual : Realization eventSignature :=
  realize eventSignature (fun _ p ω => fullTranscript p.1 ω p.2) (fun e => nomatch e)
def eventRejected : Realization eventSignature :=
  realize eventSignature (fun _ _ _ => none) (fun e => nomatch e)

private theorem eventRejected_law : ¬ eventArena.Law eventRejected := by
  intro law
  have h := (law initial initial (fun _ => 0) 0 0 [] rfl).1
  simp [eventRejected, realize] at h

def eventRecord : Registration eventArena (type_of% (@full_event_reconstruction)) where
  actual := eventActual
  bridge := Iff.rfl
  variation := ⟨full_event_reconstruction, eventRejected, eventRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eventRejected, ?_, rfl, eventRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨initial, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hletters := congrArg (fun o : FullOutput => o.map Prod.fst) h
    simpa [eventActual, realize, fullTranscript, nativeDrive, nextNative, nextOperation,
      initial, nativeStep, nativeRead, finiteRead] using hletters

def eventRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_event_reconstruction)
    (type_of% (realize eventSignature
      (fun _ p ω => fullTranscript p.1 ω p.2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.event,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.eventRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨eventArena⟩, objectArena := .source ⟨eventArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source eventArena ⟨eventRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize eventSignature
    (fun _ p ω => fullTranscript p.1 ω p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual,
    definition := none, coordinates := #[0, 3], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


private def phaseState (s : ActivePhase) : AcquiredNativeState :=
  ⟨⟨⟨.fourth (.active s), emptyRegisters⟩, 0⟩, ⟨0, 0⟩⟩

abbrev readbackSignature : Signature where
  Params := (_ : AcquiredNativeState) × ActivePhase
  State p := ValidTail p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawTail
  Anchor := Empty
  finiteAnchor := inferInstance

def readbackArena : Arena where
  signature := readbackSignature
  Law R := ∀ (c : AcquiredNativeState) (s : ActivePhase),
    c.source.finiteFields.control = .fourth (.active s) → ∀ t : ValidTail s,
    R.readout () ⟨c, s⟩ t = t.val

def readbackActual : Realization readbackSignature :=
  realize readbackSignature (fun _ p t => readbackRaw (fullRenderer p.1 p.2 t))
    (fun e => nomatch e)
def readbackRejected : Realization readbackSignature :=
  realize readbackSignature (fun _ _ _ => none) (fun e => nomatch e)

private def alphaTail : ValidTail .p := ⟨some [0], ⟨0, 0, rfl⟩⟩

private theorem readbackRejected_law : ¬ readbackArena.Law readbackRejected := by
  intro law
  have h := law (phaseState .p) .p rfl alphaTail
  simp [readbackRejected, realize, alphaTail] at h

def readbackRecord : Registration readbackArena (type_of% (@full_renderer_readback)) where
  actual := readbackActual
  bridge := Iff.rfl
  variation := ⟨full_renderer_readback, readbackRejected, readbackRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨readbackRejected, ?_, rfl, readbackRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨phaseState .p, .p⟩, ⟨none, trivial⟩, alphaTail, ?_⟩
    change readbackRaw (fullRenderer (phaseState .p) .p _) ≠
      readbackRaw (fullRenderer (phaseState .p) .p _)
    rw [full_renderer_readback _ _ rfl, full_renderer_readback _ _ rfl]
    simp [alphaTail]

abbrev deletionSignature : Signature where
  Params := AcquiredNativeState
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := FullTranscript
  Anchor := Empty
  finiteAnchor := inferInstance

def deletionArena : Arena where
  signature := deletionSignature
  Law R := ∀ (c d : AcquiredNativeState) (ω : Stream) (op : Operation),
    nextNative c ω = some (op, d) →
    deleteBlock (R.readout () c ω) = R.readout () d (rawTail ω (readCost op))

def deletionActual : Realization deletionSignature :=
  realize deletionSignature (fun _ c ω => fullTranscript c ω) (fun e => nomatch e)
def deletionRejected : Realization deletionSignature :=
  realize deletionSignature (fun _ _ _ => fullTranscript initial (fun _ => 0))
    (fun e => nomatch e)

private theorem deletionRejected_law : ¬ deletionArena.Law deletionRejected := by
  intro law
  let d : AcquiredNativeState :=
    ⟨⟨⟨.seed (some 0), emptyRegisters⟩, 0⟩, ⟨1, 0⟩⟩
  have hn : nextNative initial (fun _ => 0) = some (.read 0, d) := rfl
  have h := congrFun (law initial d (fun _ => 0) (.read 0) hn) 0
  have hl := congrArg (fun v : FullOutput => v.map (fun r => r.2.1.control)) h
  simp [deletionRejected, realize, deleteBlock, fullTranscript, nativeDrive, nextNative,
    nextOperation, initial, nativeStep, nativeRead, finiteRead, d] at hl

def deletionRecord : Registration deletionArena (type_of% (@full_delete_block)) where
  actual := deletionActual
  bridge := Iff.rfl
  variation := ⟨full_delete_block, deletionRejected, deletionRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨deletionRejected, ?_, rfl, deletionRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨initial, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hl := congrArg (fun t : FullTranscript => (t 1).map Prod.fst) h
    simpa [deletionActual, realize, fullTranscript, nativeDrive, nextNative, nextOperation,
      initial, nativeStep, nativeRead, finiteRead] using hl

abbrev pathsSignature : Signature := deletionSignature

def pathsArena : Arena where
  signature := pathsSignature
  Law R := ∀ (c : AcquiredNativeState) (s : ActivePhase),
    c.source.finiteFields.control = .fourth (.active s) → ∀ ω : Stream,
    R.readout () c ω = R.readout () c (tailStream s (stoppedReadWord s ω))

def pathsActual : Realization pathsSignature := deletionActual

def pathsRejected : Realization pathsSignature :=
  realize pathsSignature (fun _ _ ω => fun _ =>
    some ([.read (ω 1)], initial.source.finiteFields, [])) (fun e => nomatch e)

private theorem pathsRejected_law : ¬ pathsArena.Law pathsRejected := by
  intro law
  let ω : Stream := fun n => if n = 1 then 1 else 0
  have hw : stoppedReadWord .p ω = some [0] := by
    apply (stopped_word_fiber .p ω [0]).mpr
    exact ⟨by simp [Prefix, readPrefix, ω], ⟨0, 0, rfl⟩⟩
  have h := congrFun (law (phaseState .p) .p rfl ω) 0
  simp [pathsRejected, realize, hw, tailStream, wordStream, ω] at h

def pathsRecord : Registration pathsArena (type_of% (@full_renderer_all_paths)) where
  actual := pathsActual
  bridge := Iff.rfl
  variation := ⟨full_renderer_all_paths, pathsRejected, pathsRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pathsRejected, ?_, rfl, pathsRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := deletionRecord.dependence

open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open scoped ENNReal

abbrev tvSignature : Signature where
  Params := (_ : AcquiredNativeState) × (s : ActivePhase) × Measure (ValidTail s)
  State p := Measure (ValidTail p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def tvArena : Arena where
  signature := tvSignature
  Law R := ∀ (c : AcquiredNativeState) (s : ActivePhase),
    c.source.finiteFields.control = .fourth (.active s) →
    ∀ (P Q : Measure (ValidTail s)), R.readout () ⟨c, s, Q⟩ P =
      measurableTotalVariation P Q

def tvActual : Realization tvSignature :=
  realize tvSignature (fun _ p P => measurableTotalVariation
    (P.map (fullRenderer p.1 p.2.1)) (p.2.2.map (fullRenderer p.1 p.2.1)))
    (fun e => nomatch e)
def tvRejected : Realization tvSignature :=
  realize tvSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dirac_zero_positive :
    1 ≤ measurableTotalVariation (Measure.dirac (⟨none, trivial⟩ : ValidTail .p)) 0 := by
  unfold measurableTotalVariation
  apply le_iSup_of_le ⟨Set.univ, MeasurableSet.univ⟩
  simp

private theorem tvRejected_law : ¬ tvArena.Law tvRejected := by
  intro law
  have h := law (phaseState .p) .p rfl (Measure.dirac ⟨none, trivial⟩) 0
  change 0 = measurableTotalVariation (Measure.dirac (⟨none, trivial⟩ : ValidTail .p)) 0 at h
  have hp := dirac_zero_positive
  rw [← h] at hp
  exact (by simp : ¬ (1 : ℝ≥0∞) ≤ 0) hp

def tvRecord : Registration tvArena (type_of% (@full_renderer_tv)) where
  actual := tvActual
  bridge := Iff.rfl
  variation := ⟨full_renderer_tv, tvRejected, tvRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨tvRejected, ?_, rfl, tvRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨phaseState .p, .p, (0 : Measure (ValidTail .p))⟩,
      (0 : Measure (ValidTail .p)), Measure.dirac ⟨none, trivial⟩, ?_⟩
    change measurableTotalVariation ((0 : Measure (ValidTail .p)).map _) ((0 : Measure (ValidTail .p)).map _) ≠
      measurableTotalVariation ((Measure.dirac (⟨none, trivial⟩ : ValidTail .p)).map _) ((0 : Measure (ValidTail .p)).map _)
    rw [full_renderer_tv _ _ rfl, full_renderer_tv _ _ rfl]
    intro h
    have hp := dirac_zero_positive
    rw [← h] at hp
    simpa [measurableTotalVariation] using hp

def readbackRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_renderer_readback)
    (type_of% (realize readbackSignature (fun _ p t => readbackRaw (fullRenderer p.1 p.2 t)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.readback,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.readbackRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨readbackArena⟩, objectArena := .source ⟨readbackArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source readbackArena ⟨readbackRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize readbackSignature (fun _ p t => readbackRaw (fullRenderer p.1 p.2 t)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual,
    definition := none, coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def deletionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_delete_block)
    (type_of% (realize deletionSignature (fun _ c ω => fullTranscript c ω) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.deletion,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.deletionRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨deletionArena⟩, objectArena := .source ⟨deletionArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source deletionArena ⟨deletionRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize deletionSignature (fun _ c ω => fullTranscript c ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual,
    definition := none, coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def pathsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_renderer_all_paths)
    (type_of% (realize pathsSignature (fun _ c ω => fullTranscript c ω) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.paths,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.pathsRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨pathsArena⟩, objectArena := .source ⟨pathsArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source pathsArena ⟨pathsRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize pathsSignature (fun _ c ω => fullTranscript c ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual,
    definition := none, coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def tvRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_renderer_tv)
    (type_of% (realize tvSignature (fun _ p P => measurableTotalVariation (P.map (fullRenderer p.1 p.2.1)) (p.2.2.map (fullRenderer p.1 p.2.1))) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.tv,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual.tvRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨tvArena⟩, objectArena := .source ⟨tvArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source tvArena ⟨tvRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tvSignature (fun _ p P => measurableTotalVariation (P.map (fullRenderer p.1 p.2.1)) (p.2.2.map (fullRenderer p.1 p.2.1))) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual,
    definition := none, coordinates := #[0, 1, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms eventRegistration
#print axioms readbackRegistration
#print axioms deletionRegistration
#print axioms pathsRegistration
#print axioms tvRegistration

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
