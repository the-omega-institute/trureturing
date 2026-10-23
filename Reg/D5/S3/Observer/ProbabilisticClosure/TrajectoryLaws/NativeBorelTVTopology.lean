import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelTVTopology
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelTVTopology
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelTVTopology NativeBorelCommonFlow NativeFullResidual FourthSegmentStoppedLaw
open NativeConditionalControl.Tail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory

/-- The source has a phase parameter and no further state binder. -/
abbrev equalitySignature (O : ActivePhase → Type) : Signature where
  Params := ActivePhase
  State _ := Unit
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := O s
  Anchor := Empty
  finiteAnchor := inferInstance

def equalityArena (O : ActivePhase → Type) : Arena where
  signature := equalitySignature O
  Law R := ∀ s, R.readout 0 s () = R.readout 1 s ()

def topologyActual : Realization
    (equalitySignature (fun s => TopologicalSpace (ProbabilityMeasure (ValidTail s)))) :=
  realize _ (fun i s _ => if i = 0 then tvTopology s else coordinateTopology s)
    (fun e => nomatch e)

def lawBorelActual : Realization
    (equalitySignature (fun s => MeasurableSpace (ProbabilityMeasure (ValidTail s)))) :=
  realize _ (fun i s _ => if i = 0 then @borel _ (tvTopology s) else inferInstance)
    (fun e => nomatch e)

def descriptorBorelActual : Realization
    (equalitySignature (fun s => MeasurableSpace (RegularDescriptor s))) :=
  realize _ (fun i s _ => if i = 0 then @borel _ (descriptorTVTopology s) else inferInstance)
    (fun e => nomatch e)

theorem topology_bridge : (∀ s, tvTopology s = coordinateTopology s) ↔
    (equalityArena _).Law topologyActual := Iff.rfl

theorem law_borel_bridge :
    (∀ s, @borel _ (tvTopology s) =
      (inferInstance : MeasurableSpace (ProbabilityMeasure (ValidTail s)))) ↔
    (equalityArena _).Law lawBorelActual := Iff.rfl

theorem descriptor_borel_bridge :
    (∀ s, @borel _ (descriptorTVTopology s) =
      (inferInstance : MeasurableSpace (RegularDescriptor s))) ↔
    (equalityArena _).Law descriptorBorelActual := Iff.rfl

theorem topology_actual_law : (equalityArena _).Law topologyActual :=
  topology_bridge.mp tv_topology_eq_coordinates

theorem law_borel_actual_law : (equalityArena _).Law lawBorelActual :=
  law_borel_bridge.mp tv_borel_eq

theorem descriptor_borel_actual_law : (equalityArena _).Law descriptorBorelActual :=
  descriptor_borel_bridge.mp descriptor_tv_borel_eq

/-- On the literal full source telescope, the only state fiber is a singleton. -/
theorem equality_dependence_blocked (O : ActivePhase → Type)
    (R : Realization (equalitySignature O)) :
    ¬ ObservationalDependence (equalitySignature O) R := by
  intro h
  obtain ⟨s, x, y, hxy⟩ := h 0
  exact hxy (congrArg (R.readout 0 s) (Subsingleton.elim x y))

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelTVTopology
