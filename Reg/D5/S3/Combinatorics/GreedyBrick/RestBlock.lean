import D5.S3.Combinatorics.GreedyBrick.RestBlock
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.GreedyBrick.SuccessorBand
open _root_.D5.S3.Combinatorics.GreedyBrick.RestBlock

namespace Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock

abbrev signature : Signature where
  Params := Unit
  State _ := RestState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ s => placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ s : RestState, ∃ t : RestState,
    RestEventStep s t (firstZeroBin s.capacity) ∧ r.readout () () s = t.capacity.reverse

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, ht, he⟩ := h ⟨0, [], by simp⟩
  change [] = t.capacity.reverse at he
  have hl := congrArg List.length he
  have hh := ht.height_eq
  simp only [List.length_nil, List.length_reverse] at hl
  simp only [List.length_nil, firstZeroBin, max_eq_right (by omega : 0 ≤ 1)] at hh
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), ⟨0, [], by simp⟩, ⟨1, [], by simp⟩, ?_⟩
  change placeBricks 0 [] 1 ≠ placeBricks 1 [] 1
  decide

def registration : Registration arena
    (∀ s : RestState, ∃ t : RestState,
      RestEventStep s t (firstZeroBin s.capacity) ∧
        placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity) =
          t.capacity.reverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_rest_block, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Combinatorics.GreedyBrick.RestBlock.literal_rest_block in arena
  readout via (realize signature
    (fun _ _ s => placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.GreedyBrick.RestBlock
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock
