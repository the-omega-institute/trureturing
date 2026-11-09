import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Constants.Moments.CountableHankelNegativeWitness
import Reg.Support.DependentFamily

/-! Source-bound audit of the complete original theorem. -/

namespace Reg.D5.S3.Constants.Moments.CountableHankelNegativeWitness
open _root_.D5.S3.Constants.Moments.CountableHankelNegativeWitness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Polynomial
open scoped BigOperators
noncomputable section
abbrev signature : Signature where
  Params := ℝ[X]
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => p.eval₂ Complex.ofRealHom z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ p : ℝ[X], ∀ {z : ℂ}, ‖z‖ ≤ 1 →
    ‖r.readout () p z‖ ≤ ∑ k ∈ p.support, |p.coeff k|
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (z := 0) (by norm_num)
  norm_num [rejected, realize] at hb
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨X, 0, 1, ?_⟩
  simp [actual, realize]
def family : Registration arena (type_of% (@eval_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eval_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eval_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Constants.Moments.CountableHankelNegativeWitness.eval_bound_unit
  realizationName := `Reg.D5.S3.Constants.Moments.CountableHankelNegativeWitness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => p.eval₂ Complex.ofRealHom z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Constants.Moments.CountableHankelNegativeWitness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end
end Reg.D5.S3.Constants.Moments.CountableHankelNegativeWitness
