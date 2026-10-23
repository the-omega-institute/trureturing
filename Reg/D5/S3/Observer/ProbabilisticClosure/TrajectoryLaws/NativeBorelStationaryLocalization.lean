import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStationaryLocalization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStationaryLocalization
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelStationaryLocalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped ENNReal

abbrev localizationSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def localizationActual : Realization localizationSignature :=
  realize _ (fun i F Q => if i = 0 then sixthFunctional F Q
    else if i = 1 then ∫⁻ R, sixthFunctional F R ∂F.C Q else q F Q)
    (fun e => nomatch e)

def localizationArena : Arena where
  signature := localizationSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP,
    R.readout 1 F Q = R.readout 0 F Q ∧
      ENNReal.ofReal (excess Q) * R.readout 0 F Q = 0 ∧
      (R.readout 2 F Q ≠ 0 → excess Q = 0)

theorem localization_bridge : (type_of% (@common_flow_stationary_localization)) ↔
    localizationArena.Law localizationActual := Iff.rfl

theorem localization_actual_law : localizationArena.Law localizationActual :=
  localization_bridge.mp common_flow_stationary_localization

abbrev edgeSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor × PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def edgeActual : Realization edgeSignature :=
  realize _ (fun i F z => if i = 0 then sixthFunctional F z.2 else sixthFunctional F z.1)
    (fun e => nomatch e)

def edgeArena : Arena where
  signature := edgeSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP, ∀ᵐ Q' ∂F.C Q,
    R.readout 0 F (Q, Q') = R.readout 1 F (Q, Q')

theorem edge_bridge : (type_of% (@common_flow_stationary_edges)) ↔
    edgeArena.Law edgeActual := Iff.rfl

theorem edge_actual_law : edgeArena.Law edgeActual :=
  edge_bridge.mp common_flow_stationary_edges

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStationaryLocalization
