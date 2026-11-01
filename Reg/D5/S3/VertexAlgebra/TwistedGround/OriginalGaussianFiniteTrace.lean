import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
import Reg.Support.SingleDependentReadout

noncomputable section
open scoped BigOperators
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace

namespace WeightedCoordinate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ r n => (n + 1 : ℂ) * sourceValue r n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {B r : ℝ}, r ≤ B → ∀ n : ℕ,
    ‖R.readout () r n‖ ≤ traceWeightBound B n

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (B := 0) (r := 0) le_rfl 0
  norm_num [rejected, realize, traceWeightBound] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have hh := congrArg Complex.re h
  norm_num [actual, realize, sourceValue, halfBinomial, Complex.div_re] at hh
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

def evidence : Registration arena (type_of% @traceWeightValue_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceWeightValue_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@traceWeightValue_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace.WeightedCoordinate.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace.WeightedCoordinate.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r n => (n + 1 : ℂ) * sourceValue r n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WeightedCoordinate

namespace MomentBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p R => traceWeightMass R ^ 2 * R ^ p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law B := ∀ (N p : ℕ) {r R : ℝ},
    0 ≤ r → r ≤ R → R < 1 → ‖finiteTraceMoment N p r‖ ≤ B.readout () p R

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 (r := 0) (R := 0) le_rfl le_rfl (by norm_num)
  norm_num [rejected, realize, finiteTraceMoment] at hh

private theorem mass_zero : traceWeightMass 0 = 0 := by
  simp [traceWeightMass, traceWeightBound]

private theorem mass_half_pos : 0 < traceWeightMass (1 / 2) := by
  apply (traceWeightBound_summable (R := 1 / 2) (by norm_num) (by norm_num)).tsum_pos (i := 0)
  · intro n
    unfold traceWeightBound
    positivity
  · norm_num [traceWeightBound] <;> positivity

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1 / 2, ?_⟩
  change traceWeightMass 0 ^ 2 * (0 : ℝ) ^ 0 ≠
    traceWeightMass (1 / 2) ^ 2 * (1 / 2 : ℝ) ^ 0
  rw [mass_zero]
  simpa only [pow_zero, mul_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (sq_pos_of_pos mass_half_pos).ne

def evidence : Registration arena (type_of% @finiteTraceMoment_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finiteTraceMoment_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteTraceMoment_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace.MomentBound.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace.MomentBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p R => traceWeightMass R ^ 2 * R ^ p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MomentBound

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
