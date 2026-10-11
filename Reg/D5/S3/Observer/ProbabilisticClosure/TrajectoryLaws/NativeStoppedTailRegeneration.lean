import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeObserverJointLaw
open NativeInstalledFullLaw NativeFullResidual NativeStoppedTailRegeneration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open scoped ENNReal BigOperators
universe u

abbrev Outputs := RawTail × RawTail × RawTail × RawTail
abbrev streamSignature : Signature where
  Params := Unit
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Outputs
  Anchor := Empty
  finiteAnchor := inferInstance

def streamActual : Realization streamSignature := realize streamSignature
  (fun _ _ w => (stoppedReadWord .p (consStream 0 w),
    stoppedReadWord .beta (consStream 1 w),stoppedReadWord .p (consStream 1 w),
    stoppedReadWord .beta (consStream 0 w))) (fun e => nomatch e)
def streamRejected : Realization streamSignature := realize streamSignature
  (fun _ _ _ => (none,none,none,none)) (fun e => nomatch e)
def streamArena : Arena where
  signature := streamSignature
  Law R := ∀ w : Stream, R.readout () () w =
    (some [0],some [1],Option.map (List.cons 1) (stoppedReadWord .beta w),
      Option.map (List.cons 0) (stoppedReadWord .p w))

private theorem stream_actual_law : streamArena.Law streamActual := by
  intro w
  simpa only [streamActual,realize,Prod.mk.injEq] using stopped_read_cons w

private theorem stream_rejected_law : ¬ streamArena.Law streamRejected := by
  intro h
  have he := congrArg Prod.fst (h (fun _ => 0))
  change (none : RawTail) = some [0] at he
  cases he

def streamRecord : Registration streamArena (type_of% (@stopped_read_cons)) where
  actual := streamActual
  bridge := by
    constructor
    · intro h w
      simpa only [streamActual,realize,Prod.mk.injEq] using h w
    · intro h w
      simpa only [streamActual,realize,Prod.mk.injEq] using h w
  variation := ⟨stream_actual_law,streamRejected,stream_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨streamRejected,?_,rfl,stream_rejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),(fun _ => 0),(fun _ => 1),?_⟩
    intro h
    have hz : stoppedReadWord .beta (fun _ => 0) = some [0,0] := by
      apply (stopped_word_fiber _ _ _).mpr
      exact ⟨by simp [Prefix,readPrefix],0,Or.inr ⟨0,rfl⟩⟩
    have ho : stoppedReadWord .beta (fun _ => 1) = some [1] := by
      apply (stopped_word_fiber _ _ _).mpr
      exact ⟨by simp [Prefix,readPrefix],1,Or.inl ⟨rfl,rfl⟩⟩
    have he := congrArg (fun t : Outputs => t.2.2.1) h
    change stoppedReadWord .p (consStream 1 (fun _ => 0)) =
      stoppedReadWord .p (consStream 1 (fun _ => 1)) at he
    rw [(stopped_read_cons _).2.2.1,(stopped_read_cons _).2.2.1,hz,ho] at he
    cases he

abbrev Installed := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.Installed
abbrev base := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.base
abbrev baseEmitter := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.baseEmitter
local instance : Fintype base.Z := base.finite
local instance : MeasurableSpace base.Z := base.measurable
local instance : MeasurableSingletonClass base.Z := base.singletons

abbrev nativeSignature : Signature where
  Params := Installed.{u}
  State C := ActivePhase × C.complete.Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure RawTail
  Anchor := Empty
  finiteAnchor := inferInstance
def nativeActual : Realization nativeSignature := realize nativeSignature
  (fun _ C z => rawTailLaw C.complete.observer C.emitter z.1 z.2) (fun e => nomatch e)
def nativeRejected : Realization nativeSignature := realize nativeSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
def nativeArena : Arena where
  signature := nativeSignature
  Law R := ∀ C : Installed.{u},
    (∀ z : C.complete.Z,
      (C.complete.observer.project z).control = .fourth (.active .p) → ∀ E : Set RawTail,
      (R.readout () C (.p,z)).real E =
        (C.emitter.emit z (some (.read 0))).toReal * (if some [0] ∈ E then 1 else 0) +
        (1-(C.emitter.emit z (some (.read 0))).toReal) *
          ∑ z', (C.complete.observer.update (.read 1) z z').toReal *
            (rawTailLaw C.complete.observer C.emitter .beta z').real
              ((Option.map (List.cons 1)) ⁻¹' E)) ∧
    (∀ z : C.complete.Z,
      (C.complete.observer.project z).control = .fourth (.active .beta) → ∀ E : Set RawTail,
      (R.readout () C (.beta,z)).real E =
        (1-(C.emitter.emit z (some (.read 0))).toReal) * (if some [1] ∈ E then 1 else 0) +
        (C.emitter.emit z (some (.read 0))).toReal *
          ∑ z', (C.complete.observer.update (.read 0) z z').toReal *
            (rawTailLaw C.complete.observer C.emitter .p z').real
              ((Option.map (List.cons 0)) ⁻¹' E))

private theorem rejected_native : ¬ nativeArena.{u}.Law nativeRejected := by
    intro h
    let f : FiniteFields := { initial.source.finiteFields with control := .fourth (.active .p) }
    have he := (h ⟨base,baseEmitter⟩).1 (ULift.up f) rfl Set.univ
    simp only [Set.mem_univ, ite_true] at he
    change (0 : ℝ) = (PMF.pure (some (Operation.read 0)) (some (.read 0))).toReal * 1 +
      (1-(PMF.pure (some (Operation.read 0)) (some (.read 0))).toReal) * _ at he
    simpa using he

def nativeRecord : Registration nativeArena.{u}
    (type_of% (@native_stopped_tail_regeneration.{u})) where
  actual := nativeActual
  bridge := by
    constructor
    · intro h C
      exact h C.complete.observer C.emitter
    · intro h Z finite measurable singleton M e
      exact h ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩
  variation := ⟨(fun C => native_stopped_tail_regeneration C.complete.observer C.emitter),
    nativeRejected,rejected_native⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨nativeRejected,?_,rfl,rejected_native⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let f : FiniteFields := { initial.source.finiteFields with control := .fourth (.active .p) }
    refine ⟨⟨base,baseEmitter⟩,(.p,ULift.up f),(.beta,ULift.up f),?_⟩
    intro h
    have hp := (native_stopped_tail_regeneration base.observer baseEmitter).1
      (ULift.up f) rfl {some [0]}
    simp only [Set.mem_singleton_iff, ite_true] at hp
    change (rawTailLaw base.observer baseEmitter .p (ULift.up f)).real {some [0]} =
      (PMF.pure (some (Operation.read 0)) (some (.read 0))).toReal * 1 +
        (1-(PMF.pure (some (Operation.read 0)) (some (.read 0))).toReal) * _ at hp
    have hp' : (rawTailLaw base.observer baseEmitter .p (ULift.up f)).real {some [0]} = 1 :=
      by simpa using hp
    have hb : (rawTailLaw base.observer baseEmitter .beta (ULift.up f)).real {some [0]} = 0 := by
      unfold rawTailLaw
      rw [Measure.real, Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
      have hempty : (Subtype.val : ValidTail .beta → RawTail) ⁻¹' {some [0]} = ∅ := by
        ext t
        simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
        intro ht
        have hv := t.property
        rw [ht] at hv
        obtain ⟨c,hc⟩ := hv
        have hh := (parses_normal_form .beta [0] c).mpr hc
        simp [Parses,pendingColor,totalRead,legalRead] at hh
      rw [hempty]
      simp
    have he := congrArg (fun L : Measure RawTail => L.real {some [0]}) h
    change (rawTailLaw base.observer baseEmitter .p (ULift.up f)).real {some [0]} =
      (rawTailLaw base.observer baseEmitter .beta (ULift.up f)).real {some [0]} at he
    rw [hp',hb] at he
    norm_num at he

def streamRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@stopped_read_cons)
    (type_of% (realize streamSignature (fun _ _ w => (stoppedReadWord .p (consStream 0 w),
    stoppedReadWord .beta (consStream 1 w),stoppedReadWord .p (consStream 1 w),
    stoppedReadWord .beta (consStream 0 w))) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration.stream,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration.streamRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨streamArena⟩, objectArena := .source ⟨streamArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source streamArena ⟨streamRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize streamSignature (fun _ _ w => (stoppedReadWord .p (consStream 0 w),
    stoppedReadWord .beta (consStream 1 w),stoppedReadWord .p (consStream 1 w),
    stoppedReadWord .beta (consStream 0 w))) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def nativeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_stopped_tail_regeneration.{u})
    (type_of% (realize nativeSignature.{u} (fun _ C z => rawTailLaw C.complete.observer C.emitter z.1 z.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration.native,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration.nativeRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨nativeArena.{u}⟩, objectArena := .source ⟨nativeArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source nativeArena.{u} ⟨nativeRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize nativeSignature.{u} (fun _ C z => rawTailLaw C.complete.observer C.emitter z.1 z.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev projectionSignature : Signature where
  Params := ActivePhase
  State s := Measure (ValidTail s) × Measure (ValidTail s)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def projectionActual : Realization projectionSignature := realize projectionSignature
  (fun _ _ PQ => measurableTotalVariation (PQ.1.map Subtype.val) (PQ.2.map Subtype.val))
  (fun e => nomatch e)
def projectionArena : Arena where
  signature := projectionSignature
  Law R := ∀ s (P Q : Measure (ValidTail s)),
    R.readout () s (P,Q) = measurableTotalVariation P Q

theorem projectionBridge : (type_of% (@raw_projection_tv)) ↔
    projectionArena.Law projectionActual := by
  constructor <;> intro h s P Q <;> exact h s P Q

theorem projectionActualLaw : projectionArena.Law projectionActual :=
  projectionBridge.mp (@raw_projection_tv)

abbrev pureSignature : Signature where
  Params := NativeConditionalControl.DepthLaw.Depth
  State _ := ActivePhase
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure RawTail
  Anchor := Empty
  finiteAnchor := inferInstance

def pureActual : Realization pureSignature := realize pureSignature
  (fun _ k s => (NativePaidHistoryCommonRow.pureTail k s).map Subtype.val) (fun e => nomatch e)
def pureArena : Arena where
  signature := pureSignature
  Law R := ∀ k s, R.readout () k s =
    explicitStoppedWordLaw s (NativeConditionalControl.DepthLaw.rate k)

theorem pureBridge : (type_of% (@pure_raw_law)) ↔ pureArena.Law pureActual := by
  constructor <;> intro h k s <;> exact h k s

theorem pureActualLaw : pureArena.Law pureActual := pureBridge.mp (@pure_raw_law)

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration
