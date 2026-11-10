import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℝ), a 0 = 1 → 0 < a 1 →
    (∀ n, (a (n + 1)) ^ 2 ≤ a n * a (n + 2)) →
    ∀ n : ℕ, (a 1) ^ n ≤ R.readout () a n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 1) rfl (by norm_num) (fun _ => by norm_num) 0
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @logconvex_geometric_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨logconvex_geometric_lower, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(fun n => (n : ℝ)), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit_logconvex : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@logconvex_geometric_lower) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit.logconvexUnit
  realizationName := `Reg.D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit
