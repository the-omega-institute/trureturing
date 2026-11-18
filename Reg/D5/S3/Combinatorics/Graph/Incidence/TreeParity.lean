import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Incidence.TreeParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Incidence.TreeParity

open _root_.D5.S3.Combinatorics.Graph.Incidence.TreeParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph

noncomputable section

universe u

abbrev signature : Signature where
  Params := Type u
  State V := Set (V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => Nat.card s) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let x : ULift.{u} Unit := ⟨()⟩
  refine ⟨ULift.{u} Unit, {x}, ∅, ?_⟩
  change Nat.card ({x} : Set (ULift.{u} Unit)) ≠ Nat.card (∅ : Set (ULift.{u} Unit))
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_singleton, Set.ncard_empty]
  decide

/-- The original tree-realization law with its local degree as readout. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ {B : Type u} [Finite B] (S : Finset B),
    S.Nonempty → Even S.card →
      ∃ T : SimpleGraph B, T.IsTree ∧
        ∀ b : B, Odd (O.readout () B (T.neighborSet b)) ↔ b ∈ S

private theorem parityFamilyRejected : ¬ arena.{u}.Law rejected := by
  intro h
  let S : Finset (ULift.{u} Bool) := Finset.univ
  have hS : S.Nonempty := ⟨⟨false⟩, Finset.mem_univ _⟩
  have he : Even S.card := by
    simp [S]
  obtain ⟨_, _, ht⟩ := h S hS he
  have hn : Odd 0 := (ht ⟨false⟩).mpr (Finset.mem_univ _)
  exact (by decide : ¬ Odd 0) hn

def parityFamily : Registration arena.{u} (type_of% @exists_isTree_odd_neighborSet_card.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_isTree_odd_neighborSet_card.{u}, rejected, parityFamilyRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, parityFamilyRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def parityFamilyRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_isTree_odd_neighborSet_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Incidence.TreeParity.exists_isTree_odd_neighborSet_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.TreeParity.parityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨parityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => Nat.card s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.TreeParity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms parityFamilyRegistration


section

open scoped Sym2

/-- The graph and complete head function determine the indegree operation. -/
abbrev headSignature : Signature where
  Params := Σ V : Type, Σ G : SimpleGraph V, (G.edgeSet → V)
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def headActual : Realization headSignature :=
  realize headSignature (fun _ p b => indegree p.2.2 b) (fun e => nomatch e)

private def headRejected : Realization headSignature :=
  realize headSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem headDependence : ObservationalDependence headSignature headActual := by
  intro i
  let G : SimpleGraph (Fin 2) := ⊤
  let h : G.edgeSet → Fin 2 := fun _ => 0
  have hEdge : G.Adj 0 1 := by simp [G]
  have hPos : 0 < indegree h 0 := by
    let : Nonempty {e : G.edgeSet // h e = 0} := ⟨⟨⟨s(0, 1), hEdge⟩, rfl⟩⟩
    exact Nat.card_pos
  have hZero : indegree h 1 = 0 :=
    Nat.card_eq_zero.mpr (Or.inl ⟨fun e => by
      have h01 : (0 : Fin 2) = 1 := e.property
      exact (by decide : (0 : Fin 2) ≠ 1) h01⟩)
  exact ⟨⟨Fin 2, G, h⟩, 0, 1, fun he => (Nat.ne_of_gt hPos) (he.trans hZero)⟩

abbrev uniqueArena : Arena where
  signature := headSignature
  Law O := ∀ {V : Type} {G : SimpleGraph V} [Fintype V],
    G.IsTree → Odd (Nat.card V) →
      ∃! head : G.edgeSet → V, (∀ e, head e ∈ e.val) ∧
        ∀ b, Even (O.readout () ⟨V, G, head⟩ b)

abbrev branchArena : Arena where
  signature := headSignature
  Law O := ∀ {V : Type} {G : SimpleGraph V} [Fintype V]
      (_hT : G.IsTree) (_hOdd : Odd (Nat.card V)) (head : G.edgeSet → V)
      (_hhead : ∀ e, head e ∈ e.val),
    (∀ b : V, Even (O.readout () ⟨V, G, head⟩ b)) ↔
      ∀ b : V, ∀ w : G.neighborSet b,
        head ⟨s(w.val, b), G.adj_symm w.property⟩ = b ↔
          Odd (Nat.card (neighborBranch G b w).supp)

private theorem uniqueRejected : ¬ uniqueArena.Law headRejected := by
  intro h
  have hTree := isTree_pathGraph_add_one 0
  have hOdd : Odd (Nat.card (Fin 1)) := by simp
  obtain ⟨_, hGood, _⟩ := h hTree hOdd
  exact (by decide : ¬ Even 1) (hGood.2 0)

private theorem branchRejected : ¬ branchArena.Law headRejected := by
  intro h
  have hTree := isTree_pathGraph_add_one 0
  have hOdd : Odd (Nat.card (Fin 1)) := by simp
  let head : (pathGraph 1).edgeSet → Fin 1 := fun _ => 0
  have hHead (e : (pathGraph 1).edgeSet) : head e ∈ e.val := by
    obtain ⟨⟨u, v⟩, he⟩ := e
    exact ((show (pathGraph 1).Adj u v from he).ne (Subsingleton.elim _ _)).elim
  have hb (b : Fin 1) (w : (pathGraph 1).neighborSet b) :
      head ⟨s(w.val, b), (pathGraph 1).adj_symm w.property⟩ = b ↔
        Odd (Nat.card (neighborBranch (pathGraph 1) b w).supp) :=
    ((show (pathGraph 1).Adj b w.val from w.property).ne (Subsingleton.elim _ _)).elim
  exact (by decide : ¬ Even 1) (((h hTree hOdd head hHead).mpr hb) 0)

private theorem headSensitivity (law : Realization headSignature → Prop)
    (hbad : ¬ law headRejected) :
    Sensitivity ⟨headSignature, law⟩ headActual := by
  constructor
  · intro i
    refine ⟨headRejected, ?_, rfl, hbad⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim
  · intro e
    exact nomatch e

def uniqueFamily : Registration uniqueArena (type_of% @existsUnique_even_indegree_head) where
  actual := headActual
  bridge := Iff.rfl
  variation := ⟨@existsUnique_even_indegree_head, headRejected, uniqueRejected⟩
  sensitivity := headSensitivity uniqueArena.Law uniqueRejected
  dependence := headDependence

def uniqueRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@existsUnique_even_indegree_head) (Realization headSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Incidence.TreeParity.existsUnique_even_indegree_head.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.TreeParity.uniqueFamily
  realizationSource := none
  generated := false
  arena := .source ⟨uniqueArena⟩
  objectArena := .source ⟨uniqueArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source uniqueArena ⟨uniqueFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize headSignature (fun _ p b => indegree p.2.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.TreeParity
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms uniqueRegistration

def branchFamily : Registration branchArena (type_of% @even_indegrees_iff_odd_neighbor_branches) where
  actual := headActual
  bridge := Iff.rfl
  variation := ⟨@even_indegrees_iff_odd_neighbor_branches, headRejected, branchRejected⟩
  sensitivity := headSensitivity branchArena.Law branchRejected
  dependence := headDependence

def branchRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@even_indegrees_iff_odd_neighbor_branches) (Realization headSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Incidence.TreeParity.even_indegrees_iff_odd_neighbor_branches.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.TreeParity.branchFamily
  realizationSource := none
  generated := false
  arena := .source ⟨branchArena⟩
  objectArena := .source ⟨branchArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source branchArena ⟨branchFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize headSignature (fun _ p b => indegree p.2.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.TreeParity
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms branchRegistration

end

end
end Reg.D5.S3.Combinatorics.Graph.Incidence.TreeParity
