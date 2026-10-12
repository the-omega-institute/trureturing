import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.BinaryExpectationCurvature
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.BinaryExpectationCurvature
open LeanInformationAudit

set_option quotPrecheck false
noncomputable section
namespace Reg.D5.S3.Quantum.Divergence.BinaryExpectationCurvature
universe u

abbrev traceSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e)
def traceRejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => -1) (fun e => nomatch e)

variable {n : Type u} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "S" => ↥(selfAdjoint.submodule ℝ M)

def traceEntropy (R : Realization traceSignature) (Y : S) : ℝ :=
  R.readout () () (Y.val * CFC.log Y.val).trace

def defect (B A : S) : ℝ :=
  (B.val * (CFC.log B.val - CFC.log A.val)).trace.re

def bkmForm (A H : S) : ℝ :=
  (H.val * _root_.D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val).trace.re

def normalizedDirection (A H : S) (t : ℝ) : M :=
  CFC.conjSqrt (Ring.inverse (A.val + t • (1 : M))) H.val

local notation "entropy" => traceEntropy traceActual
local notation "D" => defect
local notation "BKM" => bkmForm
local notation "K" => normalizedDirection

/-- The endpoint defect's real trace varies; the contracted defect stays source-fixed. -/
def squareArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (V : unitary (Matrix n n ℂ)) (A H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (_hfixed : (V : Matrix n n ℂ) * A.val * (star V : Matrix n n ℂ) = A.val)
    (_hflip : (V : Matrix n n ℂ) * H.val * (star V : Matrix n n ℂ) = -H.val)
    (_hA : 0 ≤ A.val) (_hp : 0 ≤ (A + H).val) (_hm : 0 ≤ (A - H).val)
    (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1),
    D (A + s • H) A ≤ s ^ 2 *
      R.readout () () ((A + H).val * (CFC.log (A + H).val - CFC.log A.val)).trace

/-- The endpoint entropy-production trace varies; every original hypothesis is retained. -/
def endpointArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (V : unitary (Matrix n n ℂ)) (A H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (_hfixed : (V : Matrix n n ℂ) * A.val * (star V : Matrix n n ℂ) = A.val)
    (_hflip : (V : Matrix n n ℂ) * H.val * (star V : Matrix n n ℂ) = -H.val)
    (_hA : 0 ≤ A.val) (_hp : (A + H).val.PosDef) (_hm : 0 ≤ (A - H).val),
    2 * D (A + H) A ≤ R.readout () () (H.val * CFC.log (A + H).val).trace

/-- The first bound's input-defect trace varies; the conditional derivative bound stays fixed. -/
def expectationArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (V : unitary (Matrix n n ℂ)) (_hV : IsSelfAdjoint (V : Matrix n n ℂ))
    (rho : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) (_hrho : 0 ≤ rho.val)
    (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1),
    let sigma : Matrix n n ℂ := (1 / 2 : ℝ) • (rho.val + (V : Matrix n n ℂ) * rho.val * (star V : Matrix n n ℂ))
    let output : Matrix n n ℂ := s • rho.val + (1 - s) • sigma
    (output * (CFC.log output - CFC.log sigma)).trace.re ≤
      s ^ 2 * R.readout () () (rho.val * (CFC.log rho.val - CFC.log sigma)).trace ∧
    (rho.val.PosDef → 2 * (rho.val * (CFC.log rho.val - CFC.log sigma)).trace.re ≤
      ((rho.val - sigma) * CFC.log rho.val).trace.re)

theorem trace_dependence : ObservationalDependence traceSignature traceActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [traceActual, realize]

theorem actual_square_law : squareArena.{u}.Law traceActual := @binary_entropy_square_contraction.{u}

theorem rejected_square_law : ¬ squareArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hA : (0 : Matrix n n ℂ) ≤ A.val := Matrix.PosDef.one.posSemidef.nonneg
  have hf : (1 : unitary (Matrix n n ℂ)) * A.val * (star (1 : unitary (Matrix n n ℂ)) : Matrix n n ℂ) = A.val := by simp
  have hh0 : (1 : unitary (Matrix n n ℂ)) * (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))).val * (star (1 : unitary (Matrix n n ℂ)) : Matrix n n ℂ) = -(0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))).val := by simp
  have hm : 0 ≤ (A - 0).val := by simpa using hA
  have hp : 0 ≤ (A + 0).val := by simpa using hA
  have hh := h 1 A 0 hf hh0 hA hp hm 1 (by norm_num)
  norm_num [defect, traceRejected, realize, A, CFC.log_one] at hh

def squareEvidence : Registration squareArena.{u} (type_of% @binary_entropy_square_contraction.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_square_law, traceRejected, rejected_square_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    squareArena.Law traceActual traceRejected rejected_square_law
  dependence := trace_dependence

theorem actual_endpoint_law : endpointArena.{u}.Law traceActual := @binary_endpoint_derivative_lower_bound.{u}

theorem rejected_endpoint_law : ¬ endpointArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hA : (0 : Matrix n n ℂ) ≤ A.val := Matrix.PosDef.one.posSemidef.nonneg
  have hf : (1 : unitary (Matrix n n ℂ)) * A.val * (star (1 : unitary (Matrix n n ℂ)) : Matrix n n ℂ) = A.val := by simp
  have hh0 : (1 : unitary (Matrix n n ℂ)) * (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))).val * (star (1 : unitary (Matrix n n ℂ)) : Matrix n n ℂ) = -(0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))).val := by simp
  have hm : 0 ≤ (A - 0).val := by simpa using hA
  have hp : (A + 0).val.PosDef := by simpa using (Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef)
  have hh := h 1 A 0 hf hh0 hA hp hm
  norm_num [defect, traceRejected, realize, A, CFC.log_one] at hh

def endpointEvidence : Registration endpointArena.{u} (type_of% @binary_endpoint_derivative_lower_bound.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_endpoint_law, traceRejected, rejected_endpoint_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    endpointArena.Law traceActual traceRejected rejected_endpoint_law
  dependence := trace_dependence

theorem actual_expectation_law : expectationArena.{u}.Law traceActual := @binary_expectation_entropy_bounds.{u}

theorem rejected_expectation_law : ¬ expectationArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := 0
  have hA : (0 : Matrix n n ℂ) ≤ A.val := le_rfl
  have hh := h 1 (by simpa using (IsSelfAdjoint.one (Matrix n n ℂ))) A hA 1 (by norm_num)
  norm_num [defect, traceRejected, realize, A, CFC.log_one] at hh

def expectationEvidence : Registration expectationArena.{u} (type_of% @binary_expectation_entropy_bounds.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_expectation_law, traceRejected, rejected_expectation_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    expectationArena.Law traceActual traceRejected rejected_expectation_law
  dependence := trace_dependence

/-- Four-slot source evidence with the original theorem telescope. -/
def squareRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.BinaryExpectationCurvature.binary_entropy_square_contraction.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.BinaryExpectationCurvature.binary_entropy_square_contraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.BinaryExpectationCurvature.squareEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨squareArena.{u}⟩
  objectArena := .source ⟨squareArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareArena.{u} ⟨squareEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.BinaryExpectationCurvature
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "fn",
        "fn", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Four-slot source evidence with the original theorem telescope. -/
def endpointRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.BinaryExpectationCurvature.binary_endpoint_derivative_lower_bound.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.BinaryExpectationCurvature.binary_endpoint_derivative_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.BinaryExpectationCurvature.endpointEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨endpointArena.{u}⟩
  objectArena := .source ⟨endpointArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source endpointArena.{u} ⟨endpointEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.BinaryExpectationCurvature
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Four-slot source evidence with the original theorem telescope. -/
def expectationRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.BinaryExpectationCurvature.binary_expectation_entropy_bounds.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.BinaryExpectationCurvature.binary_expectation_entropy_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.BinaryExpectationCurvature.expectationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨expectationArena.{u}⟩
  objectArena := .source ⟨expectationArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source expectationArena.{u} ⟨expectationEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.BinaryExpectationCurvature
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Quantum.Divergence.BinaryExpectationCurvature
