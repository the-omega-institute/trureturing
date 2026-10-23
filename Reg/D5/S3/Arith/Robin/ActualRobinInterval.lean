import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualRobinInterval
import Reg.Support.DependentFamily

/- Candidate only: not compiled or declared_validated. This registers the
real logarithm readout in log_gt_one; it does not claim to cover the other
fourteen new public owner theorems or the global endpoint obligation. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.ActualRobinInterval

open _root_.D5.S3.Arith.Robin.ActualRobinInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace LogGtOne

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => Real.log (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 3 ≤ n → 1 < R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (n := 3) (by omega)
  change (1 : ℝ) < 0 at hbad
  norm_num at hbad

def family : Registration arena (type_of% (@log_gt_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_gt_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    change Real.log ((1 : ℕ) : ℝ) ≠ Real.log ((2 : ℕ) : ℝ)
    exact ne_of_lt (Real.log_lt_log (by norm_num) (by norm_num))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_gt_one)
    (type_of% (realize signature (fun _ _ n => Real.log (n : ℝ)) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualRobinInterval.log_gt_one.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualRobinInterval.LogGtOne.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => Real.log (n : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  -- Exact source state carrier, present in the original telescope/readout.
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualRobinInterval
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end LogGtOne
end Reg.D5.S3.Arith.Robin.ActualRobinInterval
