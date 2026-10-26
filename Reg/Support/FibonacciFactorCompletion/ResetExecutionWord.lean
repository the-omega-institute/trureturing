import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.Support.FibonacciFactorCompletion.ResetExecutionWord
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
noncomputable section
abbrev signature : Signature where
  Params := Return
  State _ := List (List Return)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List (List Return)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ words => words) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (R : Return) (words : List (List Return)),
    executionWord (resetConcatenation R (r.readout () R words)) = resetFactor R words

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h ⟨1,1,by decide,by decide⟩ [[]]
  change ([] : List CuLetter) = [.c,.u] at bad
  cases bad

def evidence : Registration arena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.reset_execution_word) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics.reset_execution_word,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1,1,by decide,by decide⟩,[],[[]],?_⟩
    change ([] : List (List Return)) ≠ [[]]
    simp

#print axioms evidence
end
end Reg.Support.FibonacciFactorCompletion.ResetExecutionWord
