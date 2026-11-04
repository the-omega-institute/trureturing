import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Games.DivisorNimMixedFamily
import Reg.Support.DependentFamily

/-! Faithful source registration for the native-game theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Combinatorics.Games.DivisorNimMixedFamily
open _root_.D5.S3.Combinatorics.Games.DivisorNimGrundy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ × ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : Realization signature :=
  realize signature (fun _ p n => fixedSequence (mixedPosition p.1 p.2) n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 10) (fun e => nomatch e)
abbrev formula_arena : Arena where
  signature := signature
  Law R := ∀ r s n : ℕ, 0 < r → 0 < s → R.readout () (r,s) n = mixedFormula r n
private theorem formula_rejected : ¬ formula_arena.Law rejected := by
  intro h
  have hh := h 1 1 0 (by decide) (by decide)
  change 10 = mixedFormula 1 0 at hh
  norm_num [mixedFormula] at hh
noncomputable def formula : Registration formula_arena (type_of% (@mixed_formula_statement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_formula_statement, rejected, formula_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, formula_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1,1), 1, 3, ?_⟩
    change fixedSequence (mixedPosition 1 1) 1 ≠ fixedSequence (mixedPosition 1 1) 3
    rw [mixed_formula_statement 1 1 1 (by decide) (by decide),
      mixed_formula_statement 1 1 3 (by decide) (by decide)]
    decide

noncomputable def formula_contract :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@mixed_formula_statement)
      (type_of% (realize signature (fun _ p n => fixedSequence (mixedPosition p.1 p.2) n) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimMixedFamily.formulaUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimMixedFamily.formula
  realizationSource := none
  generated := false
  arena := .source ⟨formula_arena⟩
  objectArena := .source ⟨formula_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source formula_arena ⟨formula⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => fixedSequence (mixedPosition p.1 p.2) n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.DivisorNimMixedFamily
    definition := some {
      owner := `D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
      name := `D5.S3.Combinatorics.Games.DivisorNimGrundy.MixedFormulaStatement
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Games.DivisorNimMixedFamily
