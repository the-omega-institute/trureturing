import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeFullResidual RarePriorAbsoluteRisk
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open MeasureTheory
open scoped ENNReal

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

theorem projectionBridge : (type_of% (@subtype_tv)) ↔
    projectionArena.Law projectionActual := by
  constructor <;> intro h s P Q <;> exact h s P Q

theorem projectionActualLaw : projectionArena.Law projectionActual :=
  projectionBridge.mp (@subtype_tv)

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
