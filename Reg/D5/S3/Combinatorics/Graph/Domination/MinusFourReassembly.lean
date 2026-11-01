import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly

open LeanInformationAudit
open Finset
open _root_.D5.S3.Combinatorics.Graph.DominatingSetAverage
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
open _root_.D5.S3.ConceptDynamics.InformationEscape

noncomputable section
attribute [local instance] Classical.propDecidable

def signature : DependentFamily.Signature where
  Params := ℕ
  State n := Finset (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ S => S.card) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ R.readout () n S = 0

abbrev sourceScope := type_of% (@result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, _, G, _, hs⟩ := h 0
  change (∑ S ∈ domSets G, (-4 : ℤ) ^ 0) = 0 at hs
  have hp : 0 < (domSets G).card := domSets_card_pos G
  simp only [pow_zero, sum_const, nsmul_eq_mul, mul_one] at hs
  exact (ne_of_gt (show (0 : ℤ) < (domSets G).card by exact_mod_cast hp)) hs

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    exact ⟨1, ∅, {0}, by simp [actual, DependentFamily.realize]⟩

noncomputable def registration :
    Contract.Registration (@result)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ S => S.card) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "arg",
        "fn", "arg", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end

end Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly

namespace Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.Reassembly

open LeanInformationAudit Finset
open _root_.D5.S3.Combinatorics.Graph.DominatingSetAverage
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourFamily
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourBaseStates
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
open _root_.D5.S3.ConceptDynamics.InformationEscape

noncomputable section
attribute [local instance] Classical.propDecidable

def signature : DependentFamily.Signature where
  Params := Unit
  State _ := Finset (Fin 33)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ S => S.card) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := (∑ S ∈ domSets sourceGraph, (-4 : ℤ) ^ R.readout () () S) = stateEvaluation

abbrev sourceScope := type_of% (@source_reassembly)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp source_reassembly


end
end Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly.Reassembly
