import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw ConstantSuspensionSeparator CompleteTailGeometricSurvival
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
universe u v

structure Tables where
  X : Type u
  Y : Type v
  finiteX : Fintype X
  finiteY : Fintype Y
  regular : @RegularTable X Y finiteX finiteY
attribute [instance] Tables.finiteX Tables.finiteY

abbrev survivalSignature : Signature where
  Params := Tables.{u,v}
  State C := Sum C.X C.Y
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure RawTail
  Anchor := Empty
  finiteAnchor := inferInstance

def survivalActual : Realization survivalSignature := realize survivalSignature
  (fun _ C z => Sum.elim C.regular.Q C.regular.W z) (fun e => nomatch e)
def survivalArena : Arena where
  signature := survivalSignature
  Law R := ∀ C : Tables.{u,v},
    (∀ n : ℕ, (∀ x, (R.readout () C (.inl x)).real (survivalEvent (2*n)) ≤ (4/15 : ℝ)^n) ∧
      (∀ y, (R.readout () C (.inr y)).real (survivalEvent (2*n)) ≤ (4/15 : ℝ)^n)) ∧
    (∀ x, R.readout () C (.inl x) {none} = 0) ∧
    (∀ y, R.readout () C (.inr y) {none} = 0)

theorem survivalBridge : (type_of% (@regular_complete_survival.{u,v})) ↔
    survivalArena.{u,v}.Law survivalActual := by
  constructor
  · intro h C
    exact h C.regular
  · intro h X Y finiteX finiteY R
    exact h ⟨X,Y,finiteX,finiteY,R⟩

theorem survivalActualLaw : survivalArena.{u,v}.Law survivalActual :=
  survivalBridge.mp (@regular_complete_survival.{u,v})

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival
