import D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity
open _root_.D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity (RawState)
open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m =>
    _root_.D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity.capacity m)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m →
    Finite (RawState m) ∧
    Nat.card (RawState m) = R.readout () () m ∧
    (∃ machine : DFAO Action (Option (ZMod m)) (RawState m),
      machine.CorrectOn Set.univ (atomicTask m) ∧
      ∀ q : RawState m, ∃ w : List Action, machine.toDFA.eval w = q) ∧
    (∀ (State : Type) [Fintype State]
      (machine : DFAO Action (Option (ZMod m)) State),
      machine.CorrectOn Set.univ (atomicTask m) → R.readout () () m ≤ Fintype.card State)

theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using result

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Nat.card (RawState 2) = 0 := (h 2 (by decide)).2.1
  have hc : Nat.card (RawState 2) = 9 := by
    simpa [capacity] using (result 2 (by decide)).2.1
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (2 : ℕ), (3 : ℕ), ?_⟩
    norm_num [actual, realize,
      _root_.D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity.capacity]

register_information_theorem result in arena
  readout via (realize signature (fun _ _ m =>
    _root_.D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity.capacity m)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity
