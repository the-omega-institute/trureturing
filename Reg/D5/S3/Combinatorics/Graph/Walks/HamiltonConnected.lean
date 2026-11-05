import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.HamiltonConnected

/-! Faithful dependent-family audit of the full Hamilton-connectedness telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonConnected

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.HamiltonConnected
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Classical

universe u
noncomputable section

def signature : Signature where
  Params := Type u
  State vertexType := Set vertexType
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law readout := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ),
    (∀ S : Set V, Nat.lt (readout.readout () V S) k → (G.induce Sᶜ).Connected) →
    (∀ S : Set V, G.IsIndepSet S → S.ncard < k) →
    ∀ a b : V, a ≠ b → ∃ p : G.Walk a b, p.IsHamiltonian

def rejected : Realization signature.{u} :=
  realize signature (fun _ V _ => Nat.card V + 1) (fun empty _ => Empty.elim empty)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let V : Type u := ULift.{u} (Fin 2)
  have hcard : Nat.card V = 2 := by simp [V]
  obtain ⟨p,_⟩ := law (⊥ : SimpleGraph V) 3
    (by intro S hS; change Nat.card V + 1 < 3 at hS; omega)
    (by
      intro S _
      have hle : S.ncard ≤ Nat.card V := by simpa using Set.ncard_le_ncard (Set.subset_univ S)
      omega)
    (⟨0⟩ : V) (⟨1⟩ : V) (by decide)
  have heq := SimpleGraph.reachable_bot.mp (show (⊥ : SimpleGraph V).Reachable ⟨0⟩ ⟨1⟩ from ⟨p⟩)
  exact (by decide : (⟨0⟩ : V) ≠ ⟨1⟩) heq

def family : Registration arena.{u}
    (type_of% (@exists_isHamiltonian_of_connectivity_independence.{u})) where
  actual := realize signature (fun _ _ vertices => vertices.ncard)
    (fun empty _ => Empty.elim empty)
  bridge := Iff.rfl
  variation := ⟨@exists_isHamiltonian_of_connectivity_independence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (@Subsingleton.elim Unit _ other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    let V : Type u := ULift.{u} Unit
    refine ⟨V, (∅ : Set V), ({⟨()⟩} : Set V), ?_⟩
    change (∅ : Set V).ncard ≠ ({⟨()⟩} : Set V).ncard
    simp

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_isHamiltonian_of_connectivity_independence.{u})
      (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.HamiltonConnected.exists_isHamiltonian_of_connectivity_independence.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonConnected.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ vertices => vertices.ncard)
    (fun empty _ => Empty.elim empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.HamiltonConnected
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain",
        "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonConnected
