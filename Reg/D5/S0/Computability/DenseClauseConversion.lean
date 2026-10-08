import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.DenseClauseConversion
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.DenseClauseConversion
open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.BinaryNames
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
  (fun _ _ w => Conventional.rawCount w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : List Bool,
    Nonempty (EvalsToInTime denseMachine.step (initList denseMachine w)
      (some (haltList denseMachine (denseOutput w))) (80*(w.length+1)^2)) ∧
    (denseOutput w).length ≤ w.length^2+8*w.length+7 ∧
    ClauseCodec.readWord false (denseOutput w) = some (densePrepared w) ∧
    (∀ c ∈ (densePrepared w).2, c.length ≤ 3) ∧
    unaryCount (densePrepared w).2 = R.readout () () w

def rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h Conventional.comparisonSource).2.2.2.2
  have good := (dense_word_run Conventional.comparisonSource).2.2.2.2
  have decoded : Conventional.rawCount Conventional.comparisonSource = 2 := by decide
  rw [decoded] at good
  have equal : (2 : Nat) = 3 := good.symm.trans bad
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dense_word_run,rejected,rejected_law⟩
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
    have decoded : Conventional.rawCount Conventional.comparisonSource = 2 := by decide
    change Conventional.rawCount Conventional.comparisonSource ≠ Conventional.rawCount []
    rw [decoded]
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.PredictiveThermodynamic.BinaryNames.dense_word_run) (type_of% (realize signature (fun _ _ w => Conventional.rawCount w) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Computability.DenseClauseConversion.informationUnit,
  realizationName := `Reg.D5.S0.Computability.DenseClauseConversion.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ w => Conventional.rawCount w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.DenseClauseConversion, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body","arg","arg","arg","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }] }

end Reg.D5.S0.Computability.DenseClauseConversion
