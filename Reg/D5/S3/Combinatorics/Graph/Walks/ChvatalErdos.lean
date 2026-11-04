import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.ChvatalErdos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.ChvatalErdos

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.ChvatalErdos
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
    3 ≤ Nat.card V →
    (∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) →
    (∀ S : Set V, G.IsIndepSet S → (readout.readout () V S : ℕ) ≤ k) →
    letI := Fintype.ofFinite V
    G.IsHamiltonian

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0 : ℕ)) (fun empty _ => Empty.elim empty)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let V : Type u := ULift.{u} (Fin 3)
  letI : DecidableEq V := Classical.typeDecidableEq _
  have hHamiltonian := law (⊥ : SimpleGraph V) 0
    (by simp [V, Nat.card_eq_fintype_card])
    (by intro S hS; omega) (by intro S hS; exact Nat.zero_le _)
  letI := Fintype.ofFinite V
  exact SimpleGraph.not_isHamiltonian_bot_of_card_ne_one
    (by rw [← Nat.card_eq_fintype_card]; simp [V]) hHamiltonian

def family : Registration arena.{u}
    (type_of% (@isHamiltonian_of_connectivity_independence.{u})) where
  actual := realize signature (fun _ _ vertices => vertices.ncard)
    (fun empty _ => Empty.elim empty)
  bridge := Iff.rfl
  variation := ⟨@isHamiltonian_of_connectivity_independence, rejected, rejected_law⟩
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
      (@isHamiltonian_of_connectivity_independence.{u})
      (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.ChvatalErdos.isHamiltonian_of_connectivity_independence.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.ChvatalErdos.family
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
    owner := `D5.S3.Combinatorics.Graph.Walks.ChvatalErdos
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain",
        "body", "body", "fn", "arg"]
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
end Reg.D5.S3.Combinatorics.Graph.Walks.ChvatalErdos
