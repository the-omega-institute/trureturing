import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSuperharmonic
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSuperharmonic
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelTVTopology NativeBorelSuperharmonic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Filter Topology
open scoped ENNReal

abbrev signedSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def signedActual : Realization signedSignature :=
  realize _ (fun i F Q =>
    if i = 0 then threeStepAverage F Q
    else if i = 1 then normalizedAction F (threeStepAverage F) Q
    else if i = 2 then g Q else normalizedIterate F g 3 Q) (fun e => nomatch e)

def signedArena : Arena where
  signature := signedSignature
  Law R := ∀ F,
    @Measurable _ _ (@borel _ (descriptorTVTopology .p)) inferInstance
      (fun Q => (R.readout 0 F Q).toReal) ∧
    ∀ᵐ Q ∂F.nuP,
      (3 / 25 : ℝ) ≤ (R.readout 0 F Q).toReal ∧
      (R.readout 0 F Q).toReal ≤ 1 / 2 ∧
      0 ≤ (R.readout 2 F Q).toReal - 9 / 25 ∧
      (R.readout 0 F Q).toReal - (R.readout 1 F Q).toReal =
        ((R.readout 2 F Q).toReal - (R.readout 3 F Q).toReal) / 3 ∧
      ((R.readout 2 F Q).toReal - 9 / 25) / 3 ≤
        (R.readout 0 F Q).toReal - (R.readout 1 F Q).toReal ∧
      R.readout 1 F Q ≤ R.readout 0 F Q

theorem signed_bridge : (type_of% (@common_flow_signed_h)) ↔ signedArena.Law signedActual :=
  Iff.rfl

theorem signed_actual_law : signedArena.Law signedActual :=
  signed_bridge.mp common_flow_signed_h

abbrev limitSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def limitActual : Realization limitSignature :=
  realize _ (fun i F Q n =>
    if i = 0 then qIterate F n Q
    else if i = 1 then q F Q else threeStepAverage F Q) (fun e => nomatch e)

def limitArena : Arena where
  signature := limitSignature
  Law R := ∀ F,
    Measurable (fun Q => R.readout 1 F Q 0) ∧
    ∀ᵐ Q ∂F.nuP, Antitone (R.readout 0 F Q) ∧
      Tendsto (R.readout 0 F Q) atTop (𝓝 (R.readout 1 F Q 0)) ∧
      R.readout 1 F Q 0 ≤ R.readout 2 F Q 0 ∧
      normalizedAction F (fun Q => R.readout 1 F Q 0) Q = R.readout 1 F Q 0

theorem limit_bridge : (type_of% (@common_flow_q_limit)) ↔ limitArena.Law limitActual :=
  Iff.rfl

theorem limit_actual_law : limitArena.Law limitActual :=
  limit_bridge.mp common_flow_q_limit

abbrev gainSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def gainActual : Realization gainSignature :=
  realize _ (fun i F Q => if i = 0 then sixthFunctional F Q
    else normalizedAction F (sixthFunctional F) Q) (fun e => nomatch e)

def gainArena : Arena where
  signature := gainSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP,
    R.readout 0 F Q * ENNReal.ofReal (1 + 10 * excess Q / 3) ≤ R.readout 1 F Q

theorem gain_bridge :
    (type_of% (@common_flow_sixth_power_gain)) ↔ gainArena.Law gainActual := Iff.rfl

theorem gain_actual_law : gainArena.Law gainActual :=
  gain_bridge.mp common_flow_sixth_power_gain

abbrev unweightedSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure PDescriptor × ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def unweightedActual : Realization unweightedSignature :=
  realize _ (fun i F Q => if i = 0 then
    (endpointRate⁻¹ • F.L Q, sixthFunctional F Q)
    else (ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q,
      ∫⁻ R, sixthFunctional F R ∂F.C Q)) (fun e => nomatch e)

def unweightedArena : Arena where
  signature := unweightedSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP,
    (R.readout 0 F Q).1 ≤ (R.readout 1 F Q).1 ∧
      (R.readout 0 F Q).2 + (9 / 20 : ℝ≥0∞) * ENNReal.ofReal (excess Q) *
        (R.readout 0 F Q).2 ≤ (R.readout 1 F Q).2

theorem unweighted_bridge :
    (type_of% (@common_flow_unweighted_gain)) ↔ unweightedArena.Law unweightedActual := Iff.rfl

theorem unweighted_actual_law : unweightedArena.Law unweightedActual :=
  unweighted_bridge.mp common_flow_unweighted_gain

abbrev helperSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def helperFiniteArena : Arena where
  signature := helperSignature
  Law R := ∀ F Q, R.readout 0 F Q ≠ ∞

def helperAverage : Realization helperSignature :=
  realize _ (fun _ F Q => threeStepAverage F Q) (fun e => nomatch e)

theorem helper_finite_bridge : (type_of% (@h_finite)) ↔
    helperFiniteArena.Law helperAverage := Iff.rfl

theorem helper_finite_actual_law : helperFiniteArena.Law helperAverage :=
  helper_finite_bridge.mp h_finite

def helperBoundArena : Arena where
  signature := gainSignature
  Law R := ∀ F Q, R.readout 0 F Q ≤ R.readout 1 F Q

def helperGlobalBoundArena : Arena where
  signature := helperSignature
  Law R := ∀ F Q, R.readout 0 F Q ≤ 10

def helperGlobalBound : Realization helperSignature :=
  realize _ (fun _ F Q => threeStepAverage F Q)
    (fun e => nomatch e)

def helperSixthBound : Realization gainSignature :=
  realize _ (fun i F Q => if i = 0 then sixthFunctional F Q else threeStepAverage F Q)
    (fun e => nomatch e)

theorem helper_global_bound_bridge : (type_of% (@h_global_bound)) ↔
    helperGlobalBoundArena.Law helperGlobalBound := Iff.rfl

theorem helper_global_bound_actual_law : helperGlobalBoundArena.Law helperGlobalBound :=
  helper_global_bound_bridge.mp h_global_bound

theorem helper_sixth_bound_bridge : (type_of% (@sixth_le_h)) ↔
    helperBoundArena.Law helperSixthBound := Iff.rfl

theorem helper_sixth_bound_actual_law : helperBoundArena.Law helperSixthBound :=
  helper_sixth_bound_bridge.mp sixth_le_h

def helperMeasurableArena : Arena where
  signature := helperSignature
  Law R := ∀ F, Measurable (R.readout 0 F)

def helperMeasurable : Realization helperSignature :=
  realize _ (fun _ F Q => sixthFunctional F Q) (fun e => nomatch e)

theorem helper_measurable_bridge : (type_of% (@sixth_measurable)) ↔
    helperMeasurableArena.Law helperMeasurable := Iff.rfl

theorem helper_measurable_actual_law : helperMeasurableArena.Law helperMeasurable :=
  helper_measurable_bridge.mp sixth_measurable

abbrev averageMeasurableSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def averageMeasurableActual : Realization averageMeasurableSignature :=
  realize _ (fun _ F Q => threeStepAverage F Q) (fun e => nomatch e)

def averageMeasurableArena : Arena where
  signature := averageMeasurableSignature
  Law R := ∀ F, Measurable (R.readout 0 F)

theorem averageMeasurable_bridge : (type_of% (@h_measurable)) ↔
    averageMeasurableArena.Law averageMeasurableActual := Iff.rfl

theorem averageMeasurable_actual_law : averageMeasurableArena.Law averageMeasurableActual :=
  averageMeasurable_bridge.mp h_measurable

abbrev iterateZeroSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def iterateZeroActual : Realization iterateZeroSignature :=
  realize _ (fun i F Q => if i = 0 then qIterate F 0 Q else threeStepAverage F Q) (fun e => nomatch e)

def iterateZeroArena : Arena where
  signature := iterateZeroSignature
  Law R := ∀ F Q, R.readout 0 F Q = R.readout 1 F Q

theorem iterateZero_bridge : (type_of% (@qIterate_zero)) ↔
    iterateZeroArena.Law iterateZeroActual := Iff.rfl

theorem iterateZero_actual_law : iterateZeroArena.Law iterateZeroActual :=
  iterateZero_bridge.mp qIterate_zero

abbrev distortionSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure PDescriptor
  Anchor := Empty
  finiteAnchor := inferInstance

def distortionActual : Realization distortionSignature :=
  realize _ (fun i F Q => if i = 0 then endpointRate⁻¹ • F.L Q else ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q) (fun e => nomatch e)

def distortionArena : Arena where
  signature := distortionSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP, R.readout 0 F Q ≤ R.readout 1 F Q

theorem distortion_bridge : (type_of% (@completion_distortion)) ↔
    distortionArena.Law distortionActual := Iff.rfl

theorem distortion_actual_law : distortionArena.Law distortionActual :=
  distortion_bridge.mp completion_distortion


end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSuperharmonic
