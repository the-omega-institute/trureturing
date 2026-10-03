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

register_information_theorem singleton_or_constant_query_capacity in arena
  readout via (realize signature (fun _ _ d => d + 1) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
