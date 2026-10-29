import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the skew matrix-unit sum identity. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators
open _root_.D5.S3.Quantum.Matrix.LinPsiMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock
namespace SkewSum

/-- Observe the transpose coordinate in every matrix dimension. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ) (fun n => Matrix (Fin n) (Fin n) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ T => Tᵀ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain the full skew-sum identity, including the empty dimension. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ),
    ((1 / 2 : ℝ) : ℂ) • (∑ k, ∑ l, skew k l * T * (skew k l)ᴴ) =
      T.trace • 1 - R.readout () n T

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have he := h (n := 1) 0
  simp only [rejected, realize, mul_zero, zero_mul, Finset.sum_const_zero,
    smul_zero, trace_zero, zero_smul, zero_sub] at he
  have he0 := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) he
  change (0 : ℂ) = -1 at he0
  norm_num at he0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

def family : Registration arena (type_of% @skew_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@skew_sum, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@skew_sum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinPsiMap.skew_sum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock.SkewSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => Tᵀ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end SkewSum
end Reg.D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock
