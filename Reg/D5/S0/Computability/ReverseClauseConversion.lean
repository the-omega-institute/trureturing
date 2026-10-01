import D5.S0.Computability.ReverseClauseConversion
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.ReverseClauseConversion
open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.BinaryNames
open _root_.PredictiveThermodynamic.ConventionalReverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Turing StateTransition LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ w => explicitRawCount w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : List Bool,
    Nonempty (EvalsToInTime reverseMachine.step (initList reverseMachine w)
      (some (haltList reverseMachine (convertedWord w))) (10*w.length^2+41*w.length+33)) ∧
    (convertedWord w).length ≤ 4*w.length^2+14*w.length+6 ∧
    Conventional.readWord (convertedWord w) = some (saturatedFormula (preparedFormula w).2) ∧
    Conventional.rawCount (convertedWord w) = R.readout () () w

def rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h dummySource).2.2.2
  have good := (reverse_word_run dummySource).2.2.2
  have decoded : explicitRawCount dummySource = 0 := by
    change unaryCount ([[]] : UnaryFormula 0) = 0
    simp [unaryCount,unaryStandard,Std.Sat.CNF.eval,Std.Sat.CNF.Clause.eval]
  rw [decoded] at good
  have equal : (0 : Nat) = 3 := good.symm.trans bad
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reverse_word_run,rejected,rejected_law⟩
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
    refine ⟨(),sourceWord ([] : UnaryFormula 0),dummySource,?_⟩
    have decoded : explicitRawCount dummySource = 0 := by
      change unaryCount ([[]] : UnaryFormula 0) = 0
      simp [unaryCount,unaryStandard,Std.Sat.CNF.eval,Std.Sat.CNF.Clause.eval]
    change explicitRawCount (sourceWord ([] : UnaryFormula 0)) ≠ explicitRawCount dummySource
    rw [decoded]
    change unaryCount ([] : UnaryFormula 0) ≠ 0
    simp [unaryCount,unaryStandard,Std.Sat.CNF.eval]

def selection : SourceSelection := {
  owner := `D5.S0.Computability.ReverseClauseConversion
  coordinates := #[0]
  readouts := #[
    { path := #["body","arg","arg","arg","arg"]
      stateOperand := some #["arg"] }
  ] }


register_information_theorem _root_.PredictiveThermodynamic.ConventionalReverse.reverse_word_run in arena
  readout via (realize signature (fun _ _ w => explicitRawCount w) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end Reg.D5.S0.Computability.ReverseClauseConversion
