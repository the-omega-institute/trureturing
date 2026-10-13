import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction
import D5.S3.Combinatorics.ShankarWords.OddWordConstruction
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.ShankarWords.ActualWordExtremal
open _root_.D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction

namespace Reg.D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction

abbrev signature : Signature where
  Params := ℕ
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k w => w ∈ actualWords k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (k : ℕ) (hk : 2 ≤ k) (w : List ℕ)
    (hw : r.readout () k w) (hd : descents w = extremalValue k),
    (∃ t : ℕ, 1 ≤ t ∧ k = 2 * t ∧ w = evenWord t) ∨
    (∃ t : ℕ, 1 ≤ t ∧ k = 2 * t + 1 ∧ ∃ i : OddIndex t, w = oddWord t i)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extremal_word_reconstruction, rejected, by
    intro h
    have hh := h 2 (by decide) [3,2,1] trivial (by decide)
    rcases hh with ⟨t,ht,_,he⟩ | ⟨t,ht,hk,_⟩
    · have hl := congrArg List.length he
      simp [evenWord,pairBlocks] at hl
      omega
    · omega⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · intro h
        have hh := h 2 (by decide) [3,2,1] trivial (by decide)
        rcases hh with ⟨t,ht,_,he⟩ | ⟨t,ht,hk,_⟩
        · have hl := congrArg List.length he
          simp [evenWord,pairBlocks] at hl
          omega
        · omega
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, [], evenWord 1, ?_⟩
    change (([] : List ℕ) ∈ actualWords 2) ≠ (evenWord 1 ∈ actualWords 2)
    intro h
    have hp := (even_word_construction 1 (by decide)).1
    have hn : ([] : List ℕ) ∈ actualWords 2 := by rw [h]; exact hp
    simp only [actualWords, Finset.mem_filter] at hn
    exact (by decide : ¬ (0 : ℕ) = 6) hn.2.1

def registration_contract : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@extremal_word_reconstruction)
    (type_of% (realize signature (fun _ k w => w ∈ actualWords k)
      (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str
      `D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction.extremal_word_reconstruction
      "Reg.D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction/arena")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k w => w ∈ actualWords k)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
#print axioms registration_contract

end Reg.D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction
