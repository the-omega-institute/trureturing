import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open _root_.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity

universe u

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
def arena : Arena where
  signature := signature
  Law r := ∀ {X : Type u} [Fintype X] {depth : Nat}
    (protocol : BinaryProtocol X depth)
    (identifies : Function.Injective protocol.transcript)
    (questions : ∀ (round : Fin depth) (history : Fin round.val → Bool),
      (∃ answer : Bool, ∀ x, protocol.question round history x = answer) ∨
      (Finset.univ.filter fun x : X => protocol.question round history x = true).card ≤ 1),
    Fintype.card X ≤ r.readout () () depth

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let protocol : BinaryProtocol PUnit.{u+1} 0 := {
    transcript := fun _ => 0
    question := fun round => Fin.elim0 round
    transcript_consistent := by intro x round; exact Fin.elim0 round }
  have bad := h protocol (fun x y _ => Subsingleton.elim x y)
    (by intro round; exact Fin.elim0 round)
  change Fintype.card PUnit ≤ 0 at bad
  simpa using bad

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro X inst depth protocol identifies questions
    exact singleton_or_constant_query_capacity protocol identifies questions,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (1 : Nat) ≠ 2
    decide

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.singleton_or_constant_query_capacity.{u_1}) (type_of% (arena.{u_1})) (type_of% (arena.{u_1})) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "SingletonQueryCapacity") "singleton_or_constant_query_capacity") "Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity/Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u_1})⟩,
  objectArena := ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
