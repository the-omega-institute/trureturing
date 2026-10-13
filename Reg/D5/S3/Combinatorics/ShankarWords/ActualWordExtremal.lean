import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.ShankarWords.ActualWordExtremal
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.ShankarWords.ActualWordExtremal

namespace Reg.D5.S3.Combinatorics.ShankarWords.ActualWordExtremal

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => evenWord t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ t : ℕ, 1 ≤ t →
    r.readout false () t ∈ actualWords (2 * t) ∧
      descents (r.readout true () t) = extremalValue (2 * t)

def registration : Registration arena (type_of% (@even_word_construction)) := by
  let bad (i : Bool) : Realization signature :=
    realize signature (fun j _ t => if j = i then [] else evenWord t) (fun e => nomatch e)
  have hb (i : Bool) : ¬ arena.Law (bad i) := by
    intro h
    cases i
    · have hm := (h 1 (by decide)).1
      change ([] : List ℕ) ∈ actualWords 2 at hm
      simp only [actualWords, Finset.mem_filter] at hm
      have hh := hm.2.1
      exact (by decide : ¬ (0 : ℕ) = 6) hh
    · have hh := (h 1 (by decide)).2
      change descents ([] : List ℕ) = extremalValue 2 at hh
      exact (by decide : ¬ descents ([] : List ℕ) = extremalValue 2) hh
  refine { actual := actual
           bridge := Iff.rfl
           variation := ⟨@even_word_construction, bad false, hb false⟩
           sensitivity := ?_
           dependence := ?_ }
  · constructor
    · intro i
      refine ⟨bad i, ?_, rfl, hb i⟩
      intro j hj
      funext p t
      simp [actual, bad, realize, hj]
    · intro i; exact nomatch i
  · intro i
    refine ⟨(), 0, 1, ?_⟩
    change evenWord 0 ≠ evenWord 1
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.ShankarWords.ActualWordExtremal.even_word_construction)
    (type_of% (realize signature (fun _ _ t => evenWord t) (fun e => nomatch e)))
    Type Unit := {
  unitName := `D5.S3.Combinatorics.ShankarWords.ActualWordExtremal.even_word_construction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ShankarWords.ActualWordExtremal.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => evenWord t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ShankarWords.ActualWordExtremal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
#print axioms audit

end Reg.D5.S3.Combinatorics.ShankarWords.ActualWordExtremal
