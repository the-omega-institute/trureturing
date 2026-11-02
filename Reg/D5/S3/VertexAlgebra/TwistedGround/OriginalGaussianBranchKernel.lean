import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel

/-! Source-bound audit candidates for the complete original all-index statements. -/

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPairKernel
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel
namespace Coefficients
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ n m => coeff₂ m n crossExpansion) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ m n : ℕ, R.readout () n m = if m = n then -((m : ℂ) + 1 / 2) else 0

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  norm_num [rejected, realize, pairScalar, halfBinomial] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize, crossExpansion_coeff, pairScalar, halfBinomial]
def evidence : Registration arena (type_of% @crossExpansion_coeff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@crossExpansion_coeff, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@crossExpansion_coeff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel.Coefficients.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel.Coefficients.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n m => coeff₂ m n crossExpansion) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Coefficients
namespace SourceDerivatives
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := OneSeries
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun i _ n => if i then PowerSeries.coeff n detectorBranch
    else PowerSeries.coeff n inputBranch) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout false () n =
      -PowerSeries.derivative (PowerSeries.binomialSeries ℂ (-((n : ℂ) + 1 / 2))) ∧
    R.readout true () n =
      -PowerSeries.derivative (PowerSeries.binomialSeries ℂ ((n : ℂ) + 1 / 2))

def rejectedAt (i : Bool) : Realization signature :=
  realize signature (fun j _ n => if j = i then 0 else actual.readout j () n)
    (fun e => nomatch e)
private theorem derivative_constant (z : ℂ) :
    PowerSeries.constantCoeff (PowerSeries.derivative (PowerSeries.binomialSeries ℂ z)) = z := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp [PowerSeries.binomialSeries_coeff]

private theorem rejected_fails (i : Bool) : ¬ arena.Law (rejectedAt i) := by
  intro h
  have hh := h 0
  cases i
  · have hc := congrArg (PowerSeries.coeff 0) hh.1
    norm_num [rejectedAt, realize, derivative_constant] at hc
  · have hc := congrArg (PowerSeries.coeff 0) hh.2
    norm_num [rejectedAt, realize, derivative_constant] at hc
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  cases i
  · have hc := congrArg (PowerSeries.coeff 0) h
    simp only [actual, realize, Bool.false_eq_true, ite_false] at hc
    rw [(branch_coeff_eq_negative_source_derivative 0).1,
      (branch_coeff_eq_negative_source_derivative 1).1] at hc
    norm_num [derivative_constant] at hc
  · have hc := congrArg (PowerSeries.coeff 0) h
    simp only [actual, realize, ite_true] at hc
    rw [(branch_coeff_eq_negative_source_derivative 0).2,
      (branch_coeff_eq_negative_source_derivative 1).2] at hc
    norm_num [derivative_constant] at hc

def evidence : Registration arena (type_of% @branch_coeff_eq_negative_source_derivative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@branch_coeff_eq_negative_source_derivative, rejectedAt false,
    rejected_fails false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, ?_, rejected_fails i⟩
      · intro j hji
        funext p n
        cases p
        dsimp only [rejectedAt, realize]
        split_ifs with h
        · exact (hji h).elim
        · rfl
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@branch_coeff_eq_negative_source_derivative) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel.SourceDerivatives.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel.SourceDerivatives.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i _ n => if i then PowerSeries.coeff n detectorBranch
    else PowerSeries.coeff n inputBranch) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SourceDerivatives
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel
