import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelKilledPaths NativeBorelCEvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

private instance descriptor_nonempty : Nonempty PDescriptor :=
  ⟨NativeBorelEndpointIdentification.nativeEndpoint .p true⟩
private instance original_probability (F : CommonFlow) : IsProbabilityMeasure (originalTrajectory F) := by
  unfold originalTrajectory
  infer_instance

abbrev eventSignature : Signature where
  Params := CommonFlow
  State _ := Unit
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Kernel PDescriptor (ℕ → PDescriptor)
  Anchor := Empty
  finiteAnchor := inferInstance

def eventActual : Realization eventSignature :=
  realize _ (fun _ F _ => startedC F) (fun e => nomatch e)

def harmonicArena : Arena where
  signature := eventSignature
  Law R := ∀ F, (originalTrajectory F).map shift = originalTrajectory F ∧
    shift ⁻¹' summableExcess = summableExcess ∧
    ∀ Q, (∫⁻ Q', R.readout 0 F () Q' summableExcess ∂F.C Q) =
      R.readout 0 F () Q summableExcess

theorem harmonic_bridge : (type_of% (@common_flow_event_harmonic)) ↔
    harmonicArena.Law eventActual := Iff.rfl

theorem harmonic_actual_law : harmonicArena.Law eventActual :=
  harmonic_bridge.mp common_flow_event_harmonic

def localizationArena : Arena where
  signature := eventSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP,
    ENNReal.ofReal (excess Q) * R.readout 0 F () Q summableExcess = 0 ∧
      (R.readout 0 F () Q summableExcess ≠ 0 → excess Q = 0)

theorem localization_bridge : (type_of% (@common_flow_event_localization)) ↔
    localizationArena.Law eventActual := Iff.rfl

theorem localization_actual_law : localizationArena.Law eventActual :=
  localization_bridge.mp common_flow_event_localization

def edgesArena : Arena where
  signature := eventSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP, ∀ᵐ Q' ∂F.C Q,
    R.readout 0 F () Q' summableExcess = R.readout 0 F () Q summableExcess

theorem edges_bridge : (type_of% (@common_flow_event_edges)) ↔
    edgesArena.Law eventActual := Iff.rfl

theorem edges_actual_law : edgesArena.Law eventActual :=
  edges_bridge.mp common_flow_event_edges

def conditionalArena : Arena where
  signature := eventSignature
  Law R := ∀ F,
    condDistrib (id : (ℕ → PDescriptor) → (ℕ → PDescriptor)) (fun x => x 0) (originalTrajectory F)
      =ᵐ[F.nuP] R.readout 0 F ()

theorem conditional_bridge : (type_of% (@common_flow_event_conditional)) ↔
    conditionalArena.Law eventActual := Iff.rfl

theorem conditional_actual_law : conditionalArena.Law eventActual :=
  conditional_bridge.mp common_flow_event_conditional

def markovArena : Arena where
  signature := eventSignature
  Law R := ∀ F, IsMarkovKernel (R.readout 0 F ())

theorem markov_bridge : (type_of% (@startedC_markov)) ↔ markovArena.Law eventActual := Iff.rfl

theorem markov_actual_law : markovArena.Law eventActual := markov_bridge.mp startedC_markov

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent
