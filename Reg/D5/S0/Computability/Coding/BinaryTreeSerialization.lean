import D5.S0.Computability.Coding.BinaryTreeSerialization
import Reg.Support.DependentFamily

open _root_.D5.S0.Computability.Coding.BinaryTreeSerialization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Computability.Coding.BinaryTreeSerialization

abbrev signature : Signature where
  Params := BinaryTree
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (BinaryTree × List Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ xs => parse xs) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ (t : BinaryTree) (rest : List Bool),
      r.readout () t (code t ++ rest) = some (t, rest)) ∧
    Function.Injective code ∧
    (∀ ⦃s t : BinaryTree⦄, code s <+: code t → s = t) ∧
    (∀ t : BinaryTree, parse (code t) = some (t, []))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.1 (.of false) []
  simp [rejected, realize, code] at hbad

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨.of false, [false, false], [false, true], ?_⟩
  change some (.of false, []) ≠ some (.of true, [])
  intro h
  cases h

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨serialization_spec, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem serialization_spec in arena
  readout via (realize signature (fun _ _ xs => parse xs) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S0.Computability.Coding.BinaryTreeSerialization
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S0.Computability.Coding.BinaryTreeSerialization
