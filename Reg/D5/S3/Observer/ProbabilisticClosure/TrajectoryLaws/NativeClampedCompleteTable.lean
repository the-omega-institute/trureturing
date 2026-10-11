import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeClampedCompleteTable
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeClampedCompleteTable
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeObserverJointLaw NativeInstalledFullLaw
open NativeStoppedTailRegeneration NativeClampedCompleteTable NativeConditionalControl.DepthLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory
universe u
abbrev Installed := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw.Installed

abbrev gapSignature : Signature where
  Params := Installed.{u}
  State _ := PMF Depth
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def gapActual : Realization gapSignature := realize gapSignature
  (fun _ C mu => (phaseExcess C.complete.observer C.emitter mu .p,
    phaseExcess C.complete.observer C.emitter mu .beta)) (fun e => nomatch e)
def gapArena : Arena where
  signature := gapSignature
  Law R := ∀ C : Installed.{u}, ∀ mu : PMF Depth,
    mu depthA ≠ 0 → mu depthB ≠ 0 →
    SuspendedConstant C.complete.observer C.emitter mu →
    0 ≤ (R.readout () C mu).1 ∧ 0 ≤ (R.readout () C mu).2 ∧
      1/195200 < max (R.readout () C mu).1 (R.readout () C mu).2

theorem gapBridge : (type_of% (@original_constant_suspension_gap.{u})) ↔
    gapArena.{u}.Law gapActual := by
  constructor
  · intro h C mu ha hb hc
    exact h C.complete.observer C.emitter mu ha hb hc
  · intro h Z finite measurable singleton M e mu ha hb hc
    exact h ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩ mu ha hb hc

theorem gapActualLaw : gapArena.{u}.Law gapActual :=
  gapBridge.mp (@original_constant_suspension_gap.{u})

open NativeEmissionClipping ConstantSuspensionSeparator
open scoped BigOperators
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
abbrev nativeDistortionSignature : Signature where
  Params := Installed.{u}
  State C := PMF C.complete.Z × PMF C.complete.Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ × ℝ × ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeDistortionActual : Realization nativeDistortionSignature := realize nativeDistortionSignature
  (fun _ C rows =>
    (∑ x : rows.1.support, (rows.1 x).toReal *
      |(C.emitter.emit x (some (.read 0))).toReal-
        clampEmission (C.emitter.emit x (some (.read 0))).toReal|,
     ∑ y : rows.2.support, (rows.2 y).toReal *
      |(C.emitter.emit y (some (.read 0))).toReal-
        clampEmission (C.emitter.emit y (some (.read 0))).toReal|,
     ∑ x : rows.1.support, (rows.1 x).toReal *
      (measurableTotalVariation (rawTailLaw C.complete.observer C.emitter .p x)
        (rawTailLaw C.complete.observer (clampedEmitter C.complete.observer C.emitter) .p x)).toReal,
     ∑ y : rows.2.support, (rows.2 y).toReal *
      (measurableTotalVariation (rawTailLaw C.complete.observer C.emitter .beta y)
        (rawTailLaw C.complete.observer (clampedEmitter C.complete.observer C.emitter) .beta y)).toReal))
  (fun e => nomatch e)
def nativeDistortionArena : Arena where
  signature := nativeDistortionSignature
  Law R := ∀ C : Installed.{u},
    let M := C.complete.observer
    let e := C.emitter
    ∀
    (pi tau : PMF C.complete.Z)
    (hB : pi.bind (M.update (.read 1)) = tau)
    (hA : tau.bind (M.update (.read 0)) = pi)
    (hX : ∀ z ∈ pi.support, (M.project z).control = .fourth (.active .p))
    (hY : ∀ z ∈ tau.support, (M.project z).control = .fourth (.active .beta))
    (hcB : ∀ x ∈ pi.support, ∀ y ∈ (M.update (.read 1) x).support, y ∈ tau.support)
    (hcA : ∀ y ∈ tau.support, ∀ x ∈ (M.update (.read 0) y).support, x ∈ pi.support),
    let z := R.readout () C (pi,tau)
    let du := z.1
    let dv := z.2.1
    let DQ := z.2.2.1
    let DW := z.2.2.2
    ∃ T : RegularTable pi.support tau.support,
      (∀ x, T.pi x = (pi x).toReal ∧ T.u x =
        clampEmission (e.emit x (some (.read 0))).toReal ∧
        T.Q x = rawTailLaw M (clampedEmitter M e) .p x) ∧
      (∀ y, T.tau y = (tau y).toReal ∧ T.v y =
        clampEmission (e.emit y (some (.read 0))).toReal ∧
        T.W y = rawTailLaw M (clampedEmitter M e) .beta y) ∧
      (∀ x y, T.B x y = (M.update (.read 1) x y).toReal) ∧
      (∀ y x, T.A y x = (M.update (.read 0) y x).toReal) ∧
      (DQ ≤ du+(2/3)*DW ∧ DW ≤ dv+(2/5)*DQ ∧
        DQ ≤ (15*du+10*dv)/11 ∧ DW ≤ (6*du+15*dv)/11) ∧
      (∀ x, T.Q x {none} = 0) ∧ (∀ y, T.W y {none} = 0)

theorem nativeDistortionBridge : (type_of% (@native_clamped_complete_distortion.{u})) ↔
    nativeDistortionArena.{u}.Law nativeDistortionActual := by
  constructor
  · intro h C M e pi tau hB hA hX hY hcB hcA
    exact h C.complete.observer C.emitter pi tau hB hA hX hY hcB hcA
  · intro h Z finite measurable singleton M e pi tau hB hA hX hY hcB hcA
    exact h ⟨⟨Z,finite,measurable,singleton,M⟩,e⟩ pi tau hB hA hX hY hcB hcA

theorem nativeDistortionActualLaw : nativeDistortionArena.{u}.Law nativeDistortionActual :=
  nativeDistortionBridge.mp (@native_clamped_complete_distortion.{u})

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeClampedCompleteTable
