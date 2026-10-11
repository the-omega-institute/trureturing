import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelNativeLaws
open NativeBorelEndpointIdentification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
attribute [local instance] Classical.propDecidable

abbrev coreSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor × PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def coreActual : Realization coreSignature :=
  realize _ (fun i F z => if i = 0 then sixthFunctional F z.1 else sixthFunctional F z.2)
    (fun e => nomatch e)

def coreArena : Arena where
  signature := coreSignature
  Law R := ∀ F, ∃ G : Set PDescriptor, MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    ∀ Q ∈ G, CoreAt F Q ∧
      ∀ᵐ Q' ∂F.C Q, Q' ∈ G ∧ R.readout 1 F (Q, Q') = R.readout 0 F (Q, Q')

theorem core_bridge : (type_of% (@common_flow_absorbing_core)) ↔
    coreArena.Law coreActual := Iff.rfl

theorem core_actual_law : coreArena.Law coreActual := core_bridge.mp common_flow_absorbing_core

abbrev survivingSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def survivingActual : Realization survivingSignature :=
  realize _ (fun _ F Q => q F Q) (fun e => nomatch e)

def survivingArena : Arena where
  signature := survivingSignature
  Law R := ∀ F, ∃ G : Set PDescriptor, MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    (∀ Q ∈ G, CoreAt F Q ∧
      ∀ᵐ Q' ∂F.C Q, Q' ∈ G ∧ sixthFunctional F Q' = sixthFunctional F Q) ∧
    ∀ Q ∈ G, R.readout 0 F Q ≠ 0 ↔ Q = nativeEndpoint .p true

theorem surviving_bridge : (type_of% (@common_flow_surviving_native)) ↔
    survivingArena.Law survivingActual := Iff.rfl

theorem surviving_actual_law : survivingArena.Law survivingActual :=
  surviving_bridge.mp common_flow_surviving_native

abbrev limitsSignature : Signature where
  Params := CommonFlow
  State _ := ℕ × PDescriptor
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def limitsActual : Realization limitsSignature :=
  realize _ (fun i F z => if i = 0 then q F z.2 else if i = 1 then
    q F z.2 / threeStepAverage F z.2 else coordinate z.1 1 z.2 / endpointRate ^ z.1)
    (fun e => nomatch e)

def limitsArena : Arena where
  signature := limitsSignature
  Law R := ∀ F,
    (∀ᵐ Q ∂F.nuP,
      R.readout 0 F (0, Q) = (if Q = nativeEndpoint .p true then endpointCompletion else 0) ∧
      R.readout 1 F (0, Q) = (if Q = nativeEndpoint .p true then 1 else 0)) ∧
    (∀ᵐ Q ∂F.nuP, Tendsto (fun n => R.readout 2 F (n, Q)) atTop
      (𝓝 (if Q = nativeEndpoint .p true then endpointCompletion else 0))) ∧
    Tendsto (fun n => (∫⁻ Q, coordinate n 1 Q ∂F.nuP) / endpointRate ^ n) atTop
      (𝓝 (endpointCompletion * F.nuP {nativeEndpoint .p true}))

theorem limits_bridge : (type_of% (@common_flow_upper_endpoint_limits)) ↔
    limitsArena.Law limitsActual := Iff.rfl

theorem limits_actual_law : limitsArena.Law limitsActual :=
  limits_bridge.mp common_flow_upper_endpoint_limits

abbrev transitionSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor × BDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := BDescriptor
  Anchor := Empty
  finiteAnchor := inferInstance

def transitionActual : Realization transitionSignature :=
  realize _ (fun i _ z => if i = 0 then z.2 else nativeEndpoint .beta true)
    (fun e => nomatch e)

def transitionArena : Arena where
  signature := transitionSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP, q F Q ≠ 0 →
    u Q = upper ∧ F.L Q = endpointRate • F.C Q ∧
      ∀ᵐ W ∂F.B Q, R.readout 0 F (Q, W) = R.readout 1 F (Q, W) ∧
        ∀ᵐ Q' ∂F.A W, Q' = nativeEndpoint .p true

theorem transition_bridge : (type_of% (@common_flow_surviving_transitions)) ↔
    transitionArena.Law transitionActual := Iff.rfl

theorem transition_actual_law : transitionArena.Law transitionActual :=
  transition_bridge.mp common_flow_surviving_transitions

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
