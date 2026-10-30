import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
open _root_.D5.S3.Analytic.GaussZeroBalanced.Defs
open _root_.D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature :=
  realize signature (fun _ a b => quot a b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ a b : ℝ, 0 < a → 0 < b →
    ((∀ x ∈ Ioo (0:ℝ) 1, deriv (fun β : ℝ => R.readout () a β x) b < 0) ↔
      b ≤ Real.sqrt (a*(a+1)))
private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hb : (1:ℝ) ≤ Real.sqrt (1*(1+1)) := Real.le_sqrt_of_sq_le (by norm_num)
  have hh := (h 1 1 (by norm_num) (by norm_num)).2 hb (1/2) (by constructor <;> norm_num)
  norm_num [rejected, realize] at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push_neg at h
  have heq : (fun β : ℝ => quot 1 β (1/2)) = (fun _ => quot 1 1 (1/2)) := by
    funext β
    have hh := congrFun (h 1 β 1) (1/2)
    exact hh
  have hd := (clause1 1 1 (by norm_num) (by norm_num)).2
    (Real.le_sqrt_of_sq_le (by norm_num)) (1/2) (by constructor <;> norm_num)
  rw [heq, deriv_const] at hd
  exact (lt_irrefl 0 hd)
def evidence : Registration arena (type_of% @clause1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clause1, rejected, rejected_not_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_not_law
  dependence := actual_dependence

def clause1Audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@clause1) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.ParamDeriv.clause1Unit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.ParamDeriv.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => quot a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
