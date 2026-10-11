import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailWeightedDistortion
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailWeightedDistortion
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw ConstantSuspensionSeparator CompleteTailWeightedDistortion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped BigOperators
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
universe u v
abbrev Tables := Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival.Tables

structure OriginalRows (C : Tables.{u,v}) where
  u : C.X → ℝ
  v : C.Y → ℝ
  Q : C.X → Measure RawTail
  W : C.Y → Measure RawTail
  hQ : ∀ x, IsProbabilityMeasure (Q x)
  hW : ∀ y, IsProbabilityMeasure (W y)

abbrev distortionSignature : Signature where
  Params := Tables.{u,v}
  State C := OriginalRows C
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ × ℝ × ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def distortionActual : Realization distortionSignature := realize distortionSignature
  (fun _ C O =>
    (∑ x, C.regular.pi x*|O.u x-C.regular.u x|,
     ∑ y, C.regular.tau y*|O.v y-C.regular.v y|,
     ∑ x, C.regular.pi x*(measurableTotalVariation (O.Q x) (C.regular.Q x)).toReal,
     ∑ y, C.regular.tau y*(measurableTotalVariation (O.W y) (C.regular.W y)).toReal))
  (fun e => nomatch e)
def distortionArena : Arena where
  signature := distortionSignature
  Law R := ∀ C : Tables.{u,v}, ∀ O : OriginalRows C,
    (∀ x (E : Set RawTail), (O.Q x).real E = O.u x*(if some [0] ∈ E then 1 else 0) +
      (1-O.u x)*∑ y, C.regular.B x y*(O.W y).real (prefixRaw 1 ⁻¹' E)) →
    (∀ y (E : Set RawTail), (O.W y).real E = (1-O.v y)*(if some [1] ∈ E then 1 else 0) +
      O.v y*∑ x, C.regular.A y x*(O.Q x).real (prefixRaw 0 ⁻¹' E)) →
    let z := R.readout () C O
    z.2.2.1 ≤ z.1+(2/3)*z.2.2.2 ∧ z.2.2.2 ≤ z.2.1+(2/5)*z.2.2.1 ∧
      z.2.2.1 ≤ (15*z.1+10*z.2.1)/11 ∧ z.2.2.2 ≤ (6*z.1+15*z.2.1)/11

theorem distortionBridge : (type_of% (@stationary_weighted_complete_distortion.{u,v})) ↔
    distortionArena.{u,v}.Law distortionActual := by
  constructor
  · intro h C O hq hw
    exact h C.regular O.u O.v O.Q O.W O.hQ O.hW hq hw
  · intro h X Y finiteX finiteY R u v Q W hQ hW hq hw
    exact h ⟨X,Y,finiteX,finiteY,R⟩ ⟨u,v,Q,W,hQ,hW⟩ hq hw

theorem distortionActualLaw : distortionArena.{u,v}.Law distortionActual :=
  distortionBridge.mp (@stationary_weighted_complete_distortion.{u,v})

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailWeightedDistortion
