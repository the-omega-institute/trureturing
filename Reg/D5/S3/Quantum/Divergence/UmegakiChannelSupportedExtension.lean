import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension

namespace Reg.D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section

universe u

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (N : QuantumChannel a b),
    F.readout () () (conditionalCoefficient N) (completeCoefficient N)

private abbrev Q := ULift.{u} Unit

private def identityChannel : QuantumChannel Q.{u} Q.{u} where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (StarAlgEquiv.refl ℂ (CStarMatrix Q Q ℂ))
  trace_preserving _ := rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h identityChannel

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def coefficientEqualityFamily : Registration arena.{u}
    (type_of% @conditionalCoefficient_eq_completeCoefficient.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conditionalCoefficient_eq_completeCoefficient, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def coefficientEqualityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conditionalCoefficient_eq_completeCoefficient.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension.conditionalCoefficient_eq_completeCoefficient.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension.coefficientEqualityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨coefficientEqualityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev metricArena : Arena where
  signature := signature
  Law F := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (N : QuantumChannel a b),
    F.readout () () (variationalMetricCoefficient N 0) (completeCoefficient N) ∧
    completeCoefficient N = conditionalCoefficient N ∧
    conditionalCoefficient N = sSup (variationalMetricCoefficient N '' Set.Icc 0 1)

private theorem metricRejected : ¬ metricArena.{u}.Law rejected := by
  intro h
  exact (h identityChannel).1

def metricChainFamily : Registration metricArena.{u}
    (type_of% @variationalMetricCoefficient_chain.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@variationalMetricCoefficient_chain, rejected, metricRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    metricArena.{u}.Law actual rejected metricRejected
  dependence := dependence

def metricChainAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@variationalMetricCoefficient_chain.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension.variationalMetricCoefficient_chain.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension.metricChainFamily
  realizationSource := none
  generated := false
  arena := .source ⟨metricArena.{u}⟩
  objectArena := .source ⟨metricArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source metricArena.{u} ⟨metricChainFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
