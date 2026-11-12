import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.HardCore.PartitionJoin
import Reg.Support.DependentFamily

/-! Observe the complete independent-configuration family on a variable finite domain. -/

noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.HardCore.PartitionJoin

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open _root_.D5.S3.StatisticalMechanics.HardCore.PartitionJoin
open LeanInformationAudit

attribute [local instance] Classical.propDecidable

universe u v

abbrev signature : Signature where
  Params := Σ α : Type u, Σ β : Type v, Σ _ : DecidableEq α,
    Σ _ : DecidableEq β, Σ _ : SimpleGraph α, SimpleGraph β
  State p := Finset (p.1 ⊕ p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (Finset (p.1 ⊕ p.2.1))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p U =>
    letI := p.2.2.1
    letI := p.2.2.2.1
    configurations (join p.2.2.2.2.1 p.2.2.2.2.2) U) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law O := ∀ {α : Type u} {β : Type v} [da : DecidableEq α] [db : DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (V : Finset α) (W : Finset β),
    O.readout () ⟨α, β, da, db, G, H⟩ (V.disjSum W) =
      (configurations G V).image (fun S => S.map Function.Embedding.inl) ∪
      (configurations H W).image (fun T => T.map Function.Embedding.inr)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    ⊥ ⊥ inferInstance inferInstance ∅ ∅
  change ∅ = _ at hh
  simpa [configurations, SimpleGraph.IsIndepSet, Set.Pairwise] using hh

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : signature.{u,v}.Params :=
    ⟨ULift.{u} Unit, ULift.{v} Unit, inferInstance, inferInstance, ⊥, ⊥⟩
  let x : ULift.{u} Unit ⊕ ULift.{v} Unit := Sum.inl (ULift.up ())
  refine ⟨p, ∅, {x}, ?_⟩
  intro he
  have hmem : ({x} : Finset (ULift.{u} Unit ⊕ ULift.{v} Unit)) ∈
      actual.readout i p {x} := by
    simp [actual, realize, p, configurations, SimpleGraph.IsIndepSet, Set.Pairwise]
  have hnot : ({x} : Finset (ULift.{u} Unit ⊕ ULift.{v} Unit)) ∉
      actual.readout i p ∅ := by
    simp [actual, realize, p, configurations]
  exact hnot (he.symm ▸ hmem)

def family : Registration arena.{u,v} (type_of% @configurations_join.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@configurations_join.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def configurationsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@configurations_join.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HardCore.PartitionJoin.configurationsUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HardCore.PartitionJoin.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HardCore.PartitionJoin
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms configurationsRegistration

end Reg.D5.S3.StatisticalMechanics.HardCore.PartitionJoin
