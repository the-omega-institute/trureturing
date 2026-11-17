import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.SubtreeHelly

/-! Source-bound common-membership observation for finite subtree Helly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.SubtreeHelly

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v
noncomputable section

abbrev Parameters := Σ V : Type u, Σ _G : SimpleGraph V,
  Σ I : Type v, Σ _a : I → Set V, Finset I

def signature : Signature where
  Params := Parameters.{u, v}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p x => ∀ i ∈ p.2.2.2.2, x ∈ p.2.2.2.1 i)
    (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} {I : Type v} (_hT : G.IsTree)
    {a : I → Set V} {s : Finset I}, s.Nonempty →
    (∀ i ∈ s, (G.induce (a i)).Connected) →
    (∀ i ∈ s, ∀ j ∈ s, (a i ∩ a j).Nonempty) →
    Set.Nonempty (R.readout () ⟨V, G, I, a, s⟩)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  classical
  intro h
  let V : Type u := PUnit
  let I : Type v := PUnit
  obtain ⟨x, hx⟩ := h (G := (⊥ : SimpleGraph V)) (I := I)
    IsTree.of_subsingleton (a := fun _ => Set.univ) (s := {PUnit.unit})
    (by simp) (by intro i hi; exact Connected.of_subsingleton)
    (by intro i hi j hj; exact ⟨PUnit.unit, trivial, trivial⟩)
  exact hx

def family : Registration arena.{u, v}
    (type_of% (@SimpleGraph.IsTree.inter_nonempty_of_pairwise.{u, v})) where
  actual := actual
  bridge := by
    constructor
    · intro h V G I hT a s hs hc hp
      change ∃ x, ∀ i ∈ s, x ∈ a i
      simpa only [Set.nonempty_def, Set.mem_iInter] using h hT hs hc hp
    · intro h V G I hT a s hs hc hp
      have hh : ∃ x, ∀ i ∈ s, x ∈ a i := h hT hs hc hp
      simpa only [Set.nonempty_def, Set.mem_iInter] using hh
  variation := ⟨(by
    intro V G I hT a s hs hc hp
    change ∃ x, ∀ i ∈ s, x ∈ a i
    simpa only [Set.nonempty_def, Set.mem_iInter] using hT.inter_nonempty_of_pairwise hs hc hp),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro role
    let V : Type u := ULift.{u} Bool
    let I : Type v := PUnit
    obtain ⟨T, _, _hT⟩ := (connected_top : (⊤ : SimpleGraph V).Connected).exists_isTree_le
    let a : I → Set V := fun _ => {⟨true⟩}
    refine ⟨⟨V, T, I, a, {PUnit.unit}⟩, ⟨true⟩, ⟨false⟩, ?_⟩
    change (∀ i ∈ ({PUnit.unit} : Finset I), (⟨true⟩ : V) ∈ a i) ≠
      (∀ i ∈ ({PUnit.unit} : Finset I), (⟨false⟩ : V) ∈ a i)
    simp [a]

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@SimpleGraph.IsTree.inter_nonempty_of_pairwise.{u, v})
      (Realization signature.{u, v}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.SubtreeHelly.helly_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.SubtreeHelly.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => ∀ i ∈ p.2.2.2.2, x ∈ p.2.2.2.1 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.SubtreeHelly
    definition := none
    coordinates := #[0, 1, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.Walks.SubtreeHelly
