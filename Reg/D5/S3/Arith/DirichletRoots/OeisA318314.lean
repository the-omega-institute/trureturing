import D5.S3.Arith.DirichletRoots.OeisA318314
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.DirichletRoots.OeisA318314

open _root_.D5.S3.Arith.DirichletRoots.OeisA318314
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => f n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := SourceSpec (R.readout () ()) ∧
    ∀ u : ℕ → ℚ, SourceSpec u → ∀ n, 0 < n → u n = R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1.1
  change (0 : ℚ) = 1 at hh
  norm_num at hh

def family : Registration arena (type_of% (@source_solution_unique)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_solution_unique, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change f 0 ≠ f 1
    have hz : f 0 = 0 := by rw [f]; norm_num
    rw [hz, source_solution_unique.1.1]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@source_solution_unique) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.DirichletRoots.OeisA318314.source_solution_unique.audit
  realizationName := `Reg.D5.S3.Arith.DirichletRoots.OeisA318314.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => f n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.DirichletRoots.OeisA318314
