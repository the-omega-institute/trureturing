import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.DenseClauseMachine
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.DenseClauseMachine
open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.BinaryNames
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Turing StateTransition LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option Conventional.Formula
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ w => Conventional.readWord w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => some []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : List Bool,
    Nonempty (EvalsToInTime denseMachine.step
      (initList denseMachine w)
      (some ⟨some .parseReturn, denseLocal,
        denseParserStacks (Conventional.parseStacks w [] (Conventional.decodedOccurrences w)
          [(Conventional.readWord w).isSome] [])⟩) (4*w.length+5)) ∧
    (∀ F : Conventional.Formula, R.readout () () w = some F →
      w = Conventional.formulaWord F ∧ ∀ c ∈ F, c.length ≤ 3)

def rejected_law : ¬ arena.Law rejected := by
  intro h
  have falseSpelling := ((h Conventional.comparisonSource).2 [] rfl).1
  have different : Conventional.comparisonSource ≠ Conventional.formulaWord [] := by decide
  exact different falseSpelling

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dense_parser_run,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),Conventional.comparisonSource,[],?_⟩
    change Conventional.readWord Conventional.comparisonSource ≠ Conventional.readWord []
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.PredictiveThermodynamic.BinaryNames.dense_parser_run)
    (type_of% arena) (type_of% arena)
    (type_of% (realize signature (fun _ _ w => Conventional.readWord w) (fun e => nomatch e)))
    Unit Unit Unit Unit Unit := {
  unitName := `Reg.D5.S0.Computability.DenseClauseMachine.informationUnit,
  realizationName := `Reg.D5.S0.Computability.DenseClauseMachine.registration,
  realizationSource := none, generated := false,
  arena := ⟨arena⟩, objectArena := ⟨arena⟩, catalog := Lean.Name.anonymous,
  localNames := false, realization := .source arena ⟨registration⟩,
  readout := some (realize signature (fun _ _ w => Conventional.readWord w) (fun e => nomatch e)),
  variation := none, sensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.DenseClauseMachine, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body","arg","body","domain","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }] }

end Reg.D5.S0.Computability.DenseClauseMachine
