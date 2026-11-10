import D5.S3.Arith.PolynomialValues.BackwardPropagation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.PolynomialValues.BackwardPropagation
open _root_.D5.S3.Arith.PolynomialValues.BackwardPropagation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature ℤ
  (fun _ => Polynomial ℚ) (fun _ => ℚ)
def actual : Realization signature :=
  realize signature (fun _ z p => p.eval (z : ℚ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ z p => p.eval (z : ℚ) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (H : AddSubgroup ℚ) (p : Polynomial ℚ),
    (∀ m : ℕ, p.eval (m : ℚ) ∈ H) →
    ∀ z : ℤ, r.readout () z p ∈ H

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h ⊥ 0 (by simp) 0
  change (0 : Polynomial ℚ).eval 0 + 1 ∈ (⊥ : AddSubgroup ℚ) at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (0 : Polynomial ℚ).eval 0 ≠ (1 : Polynomial ℚ).eval 0
  norm_num

def family : Registration arena (type_of% (@eval_int_mem_of_eval_nat_mem)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eval_int_mem_of_eval_nat_mem, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eval_int_mem_of_eval_nat_mem) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.PolynomialValues.BackwardPropagation.eval_int_mem_of_eval_nat_mem.__information_unit
  realizationName := `Reg.D5.S3.Arith.PolynomialValues.BackwardPropagation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z p => p.eval (z : ℚ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PolynomialValues.BackwardPropagation
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Arith.PolynomialValues.BackwardPropagation
