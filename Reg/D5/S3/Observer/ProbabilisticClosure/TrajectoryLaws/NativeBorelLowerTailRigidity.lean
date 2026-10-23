import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelLowerTailRigidity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelLowerTailRigidity
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelEndpointIdentification NativeFullResidual
open NativeBorelSignedAction NativeBorelNormalizedStability NativeBorelLowerTailRigidity
open NativeConditionalControl.Tail FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
attribute [local instance] Classical.propDecidable

abbrev iterateSignature : Signature where
  Params := CommonFlow × (PDescriptor → ℝ) × (PDescriptor → ℝ)
  State _ := ℕ × PDescriptor
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def iterateActual : Realization iterateSignature := realize _
  (fun i p z => if i = 0 then realIterate p.1 (fun Q => p.2.1 Q - p.2.2 Q) z.1 z.2
    else if i = 1 then realIterate p.1 p.2.1 z.1 z.2 else realIterate p.1 p.2.2 z.1 z.2)
  (fun e => nomatch e)

def iterateArena : Arena where
  signature := iterateSignature
  Law R := ∀ (F : CommonFlow) (f h : PDescriptor → ℝ), Bounded f → Bounded h → ∀ n,
    ∀ᵐ Q ∂F.nuP, R.readout 0 (F,f,h) (n,Q) =
      R.readout 1 (F,f,h) (n,Q) - R.readout 2 (F,f,h) (n,Q)

theorem iterate_sub_bridge : (type_of% (@iterate_sub)) ↔ iterateArena.Law iterateActual := Iff.rfl

theorem iterate_sub_actual_law : iterateArena.Law iterateActual := iterate_sub_bridge.mp iterate_sub

abbrev coordinateSignature : Signature where
  Params := CommonFlow × ℕ × Letter
  State _ := ℕ × PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateActual : Realization coordinateSignature := realize _
  (fun i p z => if i = 0 then (coordinate (p.2.1 + z.1) p.2.2 z.2).toReal
    else realIterate p.1 (fun Q => (coordinate p.2.1 p.2.2 Q).toReal) z.1 z.2)
  (fun e => nomatch e)

def coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ (F : CommonFlow) (k n : ℕ) (i : Letter),
    ∀ᵐ Q ∂F.nuP, R.readout 0 (F,k,i) (n,Q) = R.readout 1 (F,k,i) (n,Q)

theorem coordinate_iterates_bridge : (type_of% (@coordinate_iterates)) ↔
    coordinateArena.Law coordinateActual := Iff.rfl

theorem coordinate_iterates_actual_law : coordinateArena.Law coordinateActual :=
  coordinate_iterates_bridge.mp coordinate_iterates

abbrev gapSignature : Signature where
  Params := Unit
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def gapActual : Realization gapSignature := realize _ (fun _ _ Q => lowerGap Q)
  (fun e => nomatch e)

def boundedArena : Arena where
  signature := gapSignature
  Law R := Bounded (R.readout () ())

theorem bounded_lowerGap_bridge : (type_of% (@bounded_lowerGap)) ↔
    boundedArena.Law gapActual := Iff.rfl

theorem bounded_lowerGap_actual_law : boundedArena.Law gapActual :=
  bounded_lowerGap_bridge.mp bounded_lowerGap

abbrev boundSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def boundActual : Realization boundSignature := realize _
  (fun i _ Q => if i = 0 then lowerGap Q else defect false Q) (fun e => nomatch e)

def boundArena : Arena where
  signature := boundSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP,
    0 ≤ R.readout 0 F Q ∧ (2 / 9 : ℝ) ^ 3 * R.readout 1 F Q ≤ R.readout 0 F Q

theorem lowerGap_bound_bridge : (type_of% (@lowerGap_bound)) ↔ boundArena.Law boundActual := Iff.rfl

theorem lowerGap_bound_actual_law : boundArena.Law boundActual :=
  lowerGap_bound_bridge.mp lowerGap_bound

abbrev gapIterateSignature : Signature where
  Params := CommonFlow
  State _ := ℕ × PDescriptor
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def gapIterateActual : Realization gapIterateSignature := realize _
  (fun i F z => if i = 0 then realIterate F lowerGap z.1 z.2
    else if i = 1 then (coordinate (z.1 + 3) 1 z.2).toReal
    else (coordinate z.1 1 z.2).toReal) (fun e => nomatch e)

def gapIterateArena : Arena where
  signature := gapIterateSignature
  Law R := ∀ (F : CommonFlow) (n : ℕ), ∀ᵐ Q ∂F.nuP,
    R.readout 0 F (n,Q) = R.readout 1 F (n,Q) - (2 / 9 : ℝ) ^ 3 * R.readout 2 F (n,Q)

theorem lowerGap_iterates_bridge : (type_of% (@lowerGap_iterates)) ↔
    gapIterateArena.Law gapIterateActual := Iff.rfl

theorem lowerGap_iterates_actual_law : gapIterateArena.Law gapIterateActual :=
  lowerGap_iterates_bridge.mp lowerGap_iterates

abbrev completionSignature : Signature where
  Params := CommonFlow × ℕ
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def completionActual : Realization completionSignature := realize _
  (fun _ _ Q => (g Q).toReal) (fun e => nomatch e)

def completionArena : Arena where
  signature := completionSignature
  Law R := ∀ (F : CommonFlow) (n : ℕ),
    meanCoordinate F (n + 3) = (2 / 9 : ℝ) ^ 3 * meanCoordinate F n →
      ∀ᵐ Q ∂F.nuP, R.readout () (F,n) Q = 4 / 9

theorem lower_completion_bridge : (type_of% (@lower_completion)) ↔
    completionArena.Law completionActual := Iff.rfl

theorem lower_completion_actual_law : completionArena.Law completionActual :=
  lower_completion_bridge.mp lower_completion

abbrev flowSignature : Signature where
  Params := Unit
  State _ := CommonFlow
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output i _ := if i = 0 then Measure PDescriptor else if i = 1 then Measure BDescriptor
    else if i = 2 then Measure (PDescriptor × BDescriptor)
      else Measure (BDescriptor × PDescriptor)
  Anchor := Empty
  finiteAnchor := inferInstance

def flowActual : Realization flowSignature := realize _
  (fun i _ F => by
    change if i = 0 then Measure PDescriptor else if i = 1 then Measure BDescriptor
      else if i = 2 then Measure (PDescriptor × BDescriptor)
      else Measure (BDescriptor × PDescriptor)
    split_ifs
    · exact F.nuP
    · exact F.nuB
    · exact F.GammaB
    · exact F.GammaA) (fun e => nomatch e)

def lowerFlowArena : Arena where
  signature := flowSignature
  Law R := ∀ (F : CommonFlow) (n : ℕ),
    meanCoordinate F (n + 3) = (2 / 9 : ℝ) ^ 3 * meanCoordinate F n →
      R.readout 0 () F = Measure.dirac (nativeEndpoint .p false) ∧
      R.readout 1 () F = Measure.dirac (nativeEndpoint .beta false) ∧
      R.readout 2 () F = Measure.dirac (nativeEndpoint .p false, nativeEndpoint .beta false) ∧
      R.readout 3 () F = Measure.dirac (nativeEndpoint .beta false, nativeEndpoint .p false)

theorem lower_native_flow_bridge : (type_of% (@lower_native_flow)) ↔
    lowerFlowArena.Law flowActual := Iff.rfl

theorem lower_native_flow_actual_law : lowerFlowArena.Law flowActual :=
  lower_native_flow_bridge.mp lower_native_flow

abbrev successorSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor × BDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output i _ := if i = 0 then PDescriptor else BDescriptor
  Anchor := Empty
  finiteAnchor := inferInstance

def successorActual : Realization successorSignature := realize _
  (fun i _ z => by
    change if i = 0 then PDescriptor else BDescriptor
    split_ifs
    · exact z.1
    · exact z.2) (fun e => nomatch e)

def successorArena : Arena where
  signature := successorSignature
  Law R := ∀ F,
    (∀ᵐ Q ∂F.nuP, Q = nativeEndpoint .p true →
      ∀ᵐ W ∂F.B Q, R.readout 1 F (Q,W) = nativeEndpoint .beta true) ∧
    (∀ᵐ W ∂F.nuB, W = nativeEndpoint .beta true →
      ∀ᵐ Q ∂F.A W, R.readout 0 F (Q,W) = nativeEndpoint .p true)

theorem upper_native_successors_bridge : (type_of% (@upper_native_successors)) ↔
    successorArena.Law successorActual := Iff.rfl

theorem upper_native_successors_actual_law : successorArena.Law successorActual :=
  upper_native_successors_bridge.mp upper_native_successors

def edgesArena : Arena where
  signature := successorSignature
  Law R := ∀ F,
    F.nuP {nativeEndpoint .p true} = F.nuB {nativeEndpoint .beta true} ∧
    (∀ᵐ x ∂F.GammaB, R.readout 0 F x = nativeEndpoint .p true ↔
      R.readout 1 F x = nativeEndpoint .beta true) ∧
    (∀ᵐ x ∂F.GammaA, R.readout 1 F (x.2,x.1) = nativeEndpoint .beta true ↔
      R.readout 0 F (x.2,x.1) = nativeEndpoint .p true)

theorem upper_native_edges_bridge : (type_of% (@upper_native_edges)) ↔
    edgesArena.Law successorActual := Iff.rfl

theorem upper_native_edges_actual_law : edgesArena.Law successorActual :=
  upper_native_edges_bridge.mp upper_native_edges

abbrev excisionSignature : Signature where
  Params := Unit
  State _ := CommonFlow
  Role := Fin 6
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output i _ := if i = 0 then Measure PDescriptor else if i = 1 then Measure BDescriptor
    else if i = 2 then Measure (PDescriptor × BDescriptor)
    else if i = 3 then Measure (BDescriptor × PDescriptor)
    else if i = 4 then Kernel PDescriptor BDescriptor else Kernel BDescriptor PDescriptor
  Anchor := Empty
  finiteAnchor := inferInstance

def excisionActual : Realization excisionSignature := realize _
  (fun i _ F => by
    change if i = 0 then Measure PDescriptor else if i = 1 then Measure BDescriptor
      else if i = 2 then Measure (PDescriptor × BDescriptor)
      else if i = 3 then Measure (BDescriptor × PDescriptor)
      else if i = 4 then Kernel PDescriptor BDescriptor else Kernel BDescriptor PDescriptor
    split_ifs
    · exact F.nuP
    · exact F.nuB
    · exact F.GammaB
    · exact F.GammaA
    · exact F.B
    · exact F.A) (fun e => nomatch e)

def excisionArena : Arena where
  signature := excisionSignature
  Law T := ∀ (F : CommonFlow), F.nuP {nativeEndpoint .p true} < 1 →
    ∃ R : CommonFlow,
      R.nuP = (T.readout 0 () F)[|{nativeEndpoint .p true}ᶜ] ∧
      R.nuB = (T.readout 1 () F)[|{nativeEndpoint .beta true}ᶜ] ∧
      R.GammaB = (1 - F.nuP {nativeEndpoint .p true})⁻¹ •
        (T.readout 2 () F).restrict (Prod.fst ⁻¹' {nativeEndpoint .p true})ᶜ ∧
      R.GammaA = (1 - F.nuP {nativeEndpoint .p true})⁻¹ •
        (T.readout 3 () F).restrict (Prod.fst ⁻¹' {nativeEndpoint .beta true})ᶜ ∧
      R.B = T.readout 4 () F ∧ R.A = T.readout 5 () F

theorem upper_excision_bridge : (type_of% (@upper_excision)) ↔
    excisionArena.Law excisionActual := Iff.rfl

theorem upper_excision_actual_law : excisionArena.Law excisionActual :=
  upper_excision_bridge.mp upper_excision

def decompositionArena : Arena where
  signature := flowSignature
  Law T := ∀ (F : CommonFlow), F.nuP {nativeEndpoint .p true} < 1 →
    ∃ R : CommonFlow,
      R.nuP {nativeEndpoint .p true} = 0 ∧
      T.readout 0 () F = (1 - F.nuP {nativeEndpoint .p true}) • R.nuP +
        F.nuP {nativeEndpoint .p true} • Measure.dirac (nativeEndpoint .p true) ∧
      T.readout 1 () F = (1 - F.nuP {nativeEndpoint .p true}) • R.nuB +
        F.nuP {nativeEndpoint .p true} • Measure.dirac (nativeEndpoint .beta true) ∧
      T.readout 2 () F = (1 - F.nuP {nativeEndpoint .p true}) • R.GammaB +
        F.nuP {nativeEndpoint .p true} •
          Measure.dirac (nativeEndpoint .p true, nativeEndpoint .beta true) ∧
      T.readout 3 () F = (1 - F.nuP {nativeEndpoint .p true}) • R.GammaA +
        F.nuP {nativeEndpoint .p true} •
          Measure.dirac (nativeEndpoint .beta true, nativeEndpoint .p true)

theorem upper_complement_decomposition_bridge : (type_of% (@upper_complement_decomposition)) ↔
    decompositionArena.Law flowActual := Iff.rfl

theorem upper_complement_decomposition_actual_law : decompositionArena.Law flowActual :=
  upper_complement_decomposition_bridge.mp upper_complement_decomposition

def recurrenceArena : Arena where
  signature := flowSignature
  Law T := ∀ (F : CommonFlow) (N : ℕ),
    (∀ n ≥ N, meanCoordinate F (n + 2) - (2 / 9 + 6 / 25 : ℝ) * meanCoordinate F (n + 1) +
      (2 / 9 : ℝ) * (6 / 25) * meanCoordinate F n = 0) →
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      T.readout 0 () F = ENNReal.ofReal (1 - θ) • Measure.dirac (nativeEndpoint .p false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .p true) ∧
      T.readout 1 () F = ENNReal.ofReal (1 - θ) • Measure.dirac (nativeEndpoint .beta false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .beta true) ∧
      T.readout 2 () F = ENNReal.ofReal (1 - θ) •
        Measure.dirac (nativeEndpoint .p false, nativeEndpoint .beta false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .p true, nativeEndpoint .beta true) ∧
      T.readout 3 () F = ENNReal.ofReal (1 - θ) •
        Measure.dirac (nativeEndpoint .beta false, nativeEndpoint .p false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .beta true, nativeEndpoint .p true)

theorem recurrence_native_flow_bridge : (type_of% (@recurrence_native_flow)) ↔
    recurrenceArena.Law flowActual := Iff.rfl

theorem recurrence_native_flow_actual_law : recurrenceArena.Law flowActual :=
  recurrence_native_flow_bridge.mp recurrence_native_flow

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelLowerTailRigidity
