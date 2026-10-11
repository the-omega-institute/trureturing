import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeEmissionClipping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
universe u

abbrev clampSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def clampActual : Realization clampSignature := realize clampSignature
  (fun _ _ t => clampEmission t) (fun e => nomatch e)
def clampRejected : Realization clampSignature := realize clampSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
def clampArena : Arena where
  signature := clampSignature
  Law R := ∀ t : ℝ, 1/3 ≤ R.readout () () t ∧ R.readout () () t ≤ 2/5

private theorem rejected_clamp : ¬ clampArena.Law clampRejected := by
  intro h
  have he := (h 0).1
  change (1/3 : ℝ) ≤ 0 at he
  norm_num at he

def clampRecord : Registration clampArena (type_of% (@clamp_box)) where
  actual := clampActual
  bridge := by constructor <;> intro h t <;> exact h t
  variation := ⟨clamp_box,clampRejected,rejected_clamp⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨clampRejected,?_,rfl,rejected_clamp⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    change clampEmission 0 ≠ clampEmission 1
    norm_num [clampEmission]

structure Laws where
  A : Type u
  measurable : MeasurableSpace A
  P : @Measure A measurable
  R : @Measure A measurable
  T : @Measure A measurable
  pprob : @IsProbabilityMeasure A measurable P
  rprob : @IsProbabilityMeasure A measurable R
  tprob : @IsProbabilityMeasure A measurable T
attribute [instance] Laws.measurable Laws.pprob Laws.rprob Laws.tprob

abbrev budgetSignature : Signature where
  Params := Laws.{u}
  State C := {E : Set C.A // MeasurableSet E}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def budgetActual : Realization budgetSignature := realize budgetSignature
  (fun _ C E => C.T.real E.val) (fun e => nomatch e)
def budgetRejected : Realization budgetSignature := realize budgetSignature
  (fun _ _ _ => 2) (fun e => nomatch e)
def budgetArena : Arena where
  signature := budgetSignature
  Law R := ∀ C : Laws.{u}, ∀ E G : {E : Set C.A // MeasurableSet E},
    Disjoint E.val G.val → ∀ a b gap : ℝ, a ≤ b →
    C.P.real G.val = a → C.R.real G.val = b → C.P.real E.val-C.R.real E.val = gap →
    |R.readout () C G-max a (min b (R.readout () C G))| ≤
      (measurableTotalVariation C.T C.P).toReal+
        (measurableTotalVariation C.T C.R).toReal-gap

private def base : Laws.{u} where
  A := ULift.{u} Unit
  measurable := ⊤
  P := Measure.dirac (ULift.up ())
  R := Measure.dirac (ULift.up ())
  T := Measure.dirac (ULift.up ())
  pprob := by constructor; simp
  rprob := by constructor; simp
  tprob := by constructor; simp

private theorem rejected_budget : ¬ budgetArena.{u}.Law budgetRejected := by
  intro h
  have he := h base ⟨∅,MeasurableSet.empty⟩ ⟨Set.univ,MeasurableSet.univ⟩
    (by simp) 1 1 0 le_rfl (by simp) (by simp) (by simp)
  change |(2 : ℝ)-max 1 (min 1 2)| ≤
    (measurableTotalVariation base.T base.T).toReal+
      (measurableTotalVariation base.T base.T).toReal-0 at he
  norm_num [measurableTotalVariation] at he

def budgetRecord : Registration budgetArena.{u} (type_of% (@finite_event_clipping_budget.{u})) where
  actual := budgetActual
  bridge := by
    constructor
    · intro h C E G hd a b gap hab ha hb he
      exact h C.P C.R C.T E.val G.val E.property G.property hd a b gap hab ha hb he
    · intro h A measurable P R T pprob rprob tprob E G hE hG hd a b gap hab ha hb he
      exact h ⟨A,measurable,P,R,T,pprob,rprob,tprob⟩ ⟨E,hE⟩ ⟨G,hG⟩ hd a b gap hab ha hb he
  variation := ⟨(fun C E G hd a b gap hab ha hb he => finite_event_clipping_budget
    C.P C.R C.T E.val G.val E.property G.property hd a b gap hab ha hb he),
    budgetRejected,rejected_budget⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨budgetRejected,?_,rfl,rejected_budget⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨base,⟨∅,MeasurableSet.empty⟩,⟨Set.univ,MeasurableSet.univ⟩,?_⟩
    change base.T.real ∅ ≠ base.T.real Set.univ
    simp

def clampRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@clamp_box)
    (type_of% (realize clampSignature (fun _ _ t => clampEmission t) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping.clamp,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping.clampRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨clampArena⟩, objectArena := .source ⟨clampArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source clampArena ⟨clampRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize clampSignature (fun _ _ t => clampEmission t) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def budgetRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_event_clipping_budget.{u})
    (type_of% (realize budgetSignature.{u} (fun _ C E => C.T.real E.val) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping.budget,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping.budgetRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨budgetArena.{u}⟩, objectArena := .source ⟨budgetArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source budgetArena.{u} ⟨budgetRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize budgetSignature.{u} (fun _ C E => C.T.real E.val) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev Installed := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.Installed
abbrev nativeClampSignature : Signature where
  Params := Installed.{u}
  State C := FourthSegmentStoppedLaw.ActivePhase × C.complete.Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeClampActual : Realization nativeClampSignature := realize nativeClampSignature
  (fun _ C z => ((clampedEmitter C.complete.observer C.emitter).emit z.2
    (some (.read 0))).toReal) (fun e => nomatch e)
def nativeClampArena : Arena where
  signature := nativeClampSignature
  Law R := ∀ C : Installed.{u}, ∀ z s,
    (C.complete.observer.project z).control = .fourth (.active s) →
    R.readout () C (s,z) = clampEmission (C.emitter.emit z (some (.read 0))).toReal

theorem nativeClampBridge : (type_of% (@clamp_read_zero.{u})) ↔
    nativeClampArena.{u}.Law nativeClampActual := by
  constructor
  · intro h C z s hc
    exact h C.complete.observer C.emitter z s hc
  · intro h Z finite measurable singleton M e z s hc
    exact h ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩ z s hc

theorem nativeClampActualLaw : nativeClampArena.{u}.Law nativeClampActual :=
  nativeClampBridge.mp (@clamp_read_zero.{u})

def nativeBudgetActual : Realization nativeClampSignature := realize nativeClampSignature
  (fun _ C z => |(C.emitter.emit z.2 (some (.read 0))).toReal-
    ((clampedEmitter C.complete.observer C.emitter).emit z.2 (some (.read 0))).toReal|)
  (fun e => nomatch e)
def nativeBudgetArena : Arena where
  signature := nativeClampSignature
  Law R := ∀ C : Installed.{u},
    (∀ z, (C.complete.observer.project z).control = .fourth (.active .p) →
      R.readout () C (.p,z) ≤
      (measurableTotalVariation
        (NativeStoppedTailRegeneration.rawTailLaw C.complete.observer C.emitter .p z)
        (FourthSegmentStoppedLaw.explicitStoppedWordLaw .p ConstantSuspensionSeparator.endpointA)).toReal+
      (measurableTotalVariation
        (NativeStoppedTailRegeneration.rawTailLaw C.complete.observer C.emitter .p z)
        (FourthSegmentStoppedLaw.explicitStoppedWordLaw .p ConstantSuspensionSeparator.endpointB)).toReal-
        2*(1116529/22781250)) ∧
    (∀ z, (C.complete.observer.project z).control = .fourth (.active .beta) →
      R.readout () C (.beta,z) ≤
      (measurableTotalVariation
        (NativeStoppedTailRegeneration.rawTailLaw C.complete.observer C.emitter .beta z)
        (FourthSegmentStoppedLaw.explicitStoppedWordLaw .beta ConstantSuspensionSeparator.endpointA)).toReal+
      (measurableTotalVariation
        (NativeStoppedTailRegeneration.rawTailLaw C.complete.observer C.emitter .beta z)
        (FourthSegmentStoppedLaw.explicitStoppedWordLaw .beta ConstantSuspensionSeparator.endpointB)).toReal-
        2*(239/6750))

theorem nativeBudgetBridge : (type_of% (@native_configuration_clipping_budget.{u})) ↔
    nativeBudgetArena.{u}.Law nativeBudgetActual := by
  constructor
  · intro h C
    exact h C.complete.observer C.emitter
  · intro h Z finite measurable singleton M e
    exact h ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩

theorem nativeBudgetActualLaw : nativeBudgetArena.{u}.Law nativeBudgetActual :=
  nativeBudgetBridge.mp (@native_configuration_clipping_budget.{u})

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping
