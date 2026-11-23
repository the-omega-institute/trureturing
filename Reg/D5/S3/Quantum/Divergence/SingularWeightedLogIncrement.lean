import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.SingularWeightedLogIncrement

/-! Source-bound audit of the equality test on the weighted logarithm increment. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Divergence.SingularWeightedLogIncrement

open _root_.Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.SingularWeightedLogIncrement

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A C ρ : Matrix (Fin n) (Fin n) ℂ} {u v e : ℝ}
    (_ : C.PosSemidef) (_ : ρ.PosSemidef) (_ : 0 < u) (_ : u ≤ v) (_ : 0 < e)
    (_ : u • C ≤ A) (_ : A ≤ v • C),
    0 ≤ (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re ∧
      (R.readout () () (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re 0 ↔ C * ρ = 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlow : (1 : ℝ) • (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 0 := by simp
  have hhigh : (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ (1 : ℝ) • 0 := by simp
  have hz := @h 1 0 0 0 1 1 1 Matrix.PosSemidef.zero Matrix.PosSemidef.zero zero_lt_one
    le_rfl zero_lt_one hlow hhigh
  exact hz.2.mpr (Matrix.zero_mul _)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, fun h => ?_⟩
  have hz := congrFun h 0
  change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at hz
  exact one_ne_zero (hz ▸ rfl)

def family : Registration arena (type_of% @weighted_log_increment_nonneg_and_eq_zero_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_log_increment_nonneg_and_eq_zero_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_log_increment_nonneg_and_eq_zero_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.SingularWeightedLogIncrement.weighted_log_increment_nonneg_and_eq_zero_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.SingularWeightedLogIncrement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.SingularWeightedLogIncrement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.SingularWeightedLogIncrement
