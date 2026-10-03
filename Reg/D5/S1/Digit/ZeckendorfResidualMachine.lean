import LeanInformationAuditInterface.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.ZeckendorfResidualMachine
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.ZeckendorfResidualMachine

namespace Reg.D5.S1.Digit.ZeckendorfResidualMachine
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ c => c) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ c, Finite (ResidualState c) ∧
    Admissible c (R.readout () () (Nat.card (ResidualState c)))

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad : ¬ Admissible 0 0 := by
    intro hz
    obtain ⟨P, output, hzero, heq, hreach⟩ := hz
    exact Fin.elim0 P.start
  apply bad
  simpa [rejected, realize] using (h 0).2

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_residual_realization,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    simpa [actual, realize] using he

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Digit.ZeckendorfResidualMachine
  coordinates := #[]
  readouts := #[{path := #["body","arg","fn","arg"], stateBinder := 0}] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Digit.ZeckendorfResidualMachine.finite_residual_realization) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ c => c) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfResidualMachine") "finite_residual_realization") "Reg.D5.S1.Digit.ZeckendorfResidualMachine/Reg.D5.S1.Digit.ZeckendorfResidualMachine.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfResidualMachine.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ c => c) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfResidualMachine, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfResidualMachine
