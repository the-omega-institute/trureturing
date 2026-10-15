import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Computability.UnrestrictedClauseWords
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.UnrestrictedClauseWords
open _root_.PredictiveThermodynamic.Unrestricted
open _root_.PredictiveThermodynamic.Conventional
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Turing StateTransition

namespace Codec

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option Formula
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ _ w => _root_.PredictiveThermodynamic.Unrestricted.readWord w)
    (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ w F,
    R.readout () () w = some F ↔ Canonical F ∧ w = formulaWord F

abbrev sourceScope := type_of% (@word_codec)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => none) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have bad := (h [false,false] []).mpr ⟨by simp [Canonical],rfl⟩
  cases bad

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨word_codec, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(), [], [false,false], ?_⟩
    change (none : Option Formula) ≠ some []
    decide

/-- The family proof retains the full word/formula telescope and selects the
original total decoder observation on its unbounded word state. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@word_codec) (DependentFamily.Realization signature) Unit Unit where
  unitName := `PredictiveThermodynamic.Unrestricted.word_codec.__information_unit
  realizationName := `Reg.D5.S0.Computability.UnrestrictedClauseWords.Codec.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ w => _root_.PredictiveThermodynamic.Unrestricted.readWord w)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.UnrestrictedClauseWords
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Codec

namespace Parser

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Option Formula
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ F => resultWord F) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ w,
    Nonempty (TM2OutputsInTime parser w
      (some (R.readout () () (_root_.PredictiveThermodynamic.Unrestricted.readWord w)))
      (2 * w.length + 3))

abbrev sourceScope := type_of% (@parser_run)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => []) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨bad⟩ := h []
  have bound : bad.steps ≤ 3 := bad.steps_le_m
  have trace := bad.evals_in_steps
  change (flip bind parser.step)^[bad.steps] (some (initList parser [])) =
    some (haltList parser []) at trace
  let observe : Option parser.Cfg → Option (Option Label × List Bool) :=
    fun c => c.map (fun c => (c.l,c.stk Stack.output))
  have small : ∀ k : Nat, k ≤ 3 →
      observe ((flip bind parser.step)^[k] (some (initList parser []))) ≠ some (none,[]) := by
    intro k hk
    interval_cases k <;> decide
  exact small bad.steps bound (congrArg observe trace)

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨parser_run, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(), none, some [], ?_⟩
    change ([false] : List Bool) ≠ [true,false,false]
    decide

/-- The readout is the original encoded result on the exact decoded-formula
operand of the charged parser statement. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@parser_run) (DependentFamily.Realization signature) Unit Unit where
  unitName := `PredictiveThermodynamic.Unrestricted.parser_run.__information_unit
  realizationName := `Reg.D5.S0.Computability.UnrestrictedClauseWords.Parser.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ F => resultWord F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.UnrestrictedClauseWords
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Parser
end Reg.D5.S0.Computability.UnrestrictedClauseWords
