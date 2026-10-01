import D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum
open _root_.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
  (WordRepresentation wordMap wordBehavior integerTask integerFieldTask)
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open _root_.D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
open _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
open _root_.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound (wordOperator)
open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum
universe u

abbrev signature : Signature where
  Params := Σ K : Type u, Field K
  State _ := List Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p w => @integerFieldTask p.1 p.2 w) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2; (0, 0)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [field : Field K],
    (∀ w : List Window, wordBehavior (sixDimensional K) w = R.readout () ⟨K, field⟩ w) ∧
    Module.finrank K (SixState K) = 6 ∧
    LinearIndependent K (fun j : Fin 6 =>
      wordMap (sixDimensional K).transition (sixPrefixes j) (sixDimensional K).initial) ∧
    Submodule.span K (Set.range (fun w : List Window =>
      wordMap (sixDimensional K).transition w (sixDimensional K).initial)) = ⊤

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := (h (ULift.{u} ℚ)).1 []
  simpa [rejected, realize, wordBehavior, sixDimensional, wordMap, wordOperator,
    sixOutput] using hz

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    refine ⟨⟨ULift.{u} ℚ, inferInstance⟩, ([] : List Window), ([.low, .high] : List Window), ?_⟩
    norm_num [actual, realize, integerFieldTask, integerTask, task, DFAO.evalOutput,
      rawMachine, DFA.eval, DFA.evalFrom, rawOutput, rawTransition, clock, step,
      displacement, first, last, quantity]

register_information_theorem _root_.D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum.result in arena
  readout via (realize signature (fun _ p w => @integerFieldTask p.1 p.2 w)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.FiveWindowFieldLinearMinimum
