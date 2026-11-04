import D5.S3.Combinatorics.Graph.Laman.PlanarLaman
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! # The spanning Laman observation over arbitrary finite graph carriers -/

namespace Reg.D5.S3.Combinatorics.Graph.Laman.PlanarLaman

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open SimpleGraph

universe u

set_option backward.isDefEq.respectTransparency false

noncomputable section

abbrev signature : DependentFamily.Signature where
  Params := Type u
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u}
    (fun _ _ G => ∃ H, H ≤ G ∧ H.IsLaman) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hV : 2 ≤ Nat.card V),
    G.IsGenericallyRigid 2 ↔ R.readout () V G

abbrev sourceScope := type_of% (@isGenericallyRigid_two_iff_exists_isLaman_le.{u})

private theorem source_bridge : sourceScope.{u} ↔ (arena.{u}).Law actual.{u} := Iff.rfl

private theorem base_rigid :
    (⊤ : SimpleGraph (ULift.{u} (Fin 2))).IsGenericallyRigid 2 := by
  exact ((top_fin_two_isGenericallyRigidInj 1).iso
    (Iso.completeGraph Equiv.ulift.symm)).toIsGenericallyRigid

private theorem base_spanning :
    ∃ H : SimpleGraph (ULift.{u} (Fin 2)), H ≤ ⊤ ∧ H.IsLaman := by
  exact ⟨⊤, le_rfl, top_fin_two_isLaman.iso (Iso.completeGraph Equiv.ulift.symm)⟩

private theorem bot_not_spanning :
    ¬ ∃ H : SimpleGraph (ULift.{u} (Fin 2)), H ≤ ⊥ ∧ H.IsLaman := by
  rintro ⟨H, hH, hLam⟩
  have hH_bot : H = ⊥ := le_bot_iff.mp hH
  have hc := hLam.edgeSet_ncard
  rw [hH_bot] at hc
  norm_num at hc

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ (arena.{u}).Law rejected.{u} := by
  intro h
  exact (h (G := (⊤ : SimpleGraph (ULift.{u} (Fin 2)))) (by norm_num)).mp base_rigid

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
  actual := actual.{u}
  bridge := source_bridge.{u}
  variation := ⟨@isGenericallyRigid_two_iff_exists_isLaman_le.{u}, rejected.{u}, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u}, ?_, rfl, rejected_law.{u}⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} (Fin 2), ⊤, ⊥, ?_⟩
    change (∃ H : SimpleGraph (ULift.{u} (Fin 2)), H ≤ ⊤ ∧ H.IsLaman) ≠
      (∃ H : SimpleGraph (ULift.{u} (Fin 2)), H ≤ ⊥ ∧ H.IsLaman)
    intro he
    exact bot_not_spanning (he ▸ base_spanning)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@isGenericallyRigid_two_iff_exists_isLaman_le.{u})
      (DependentFamily.Realization signature.{u}) (Type u) Unit where
  unitName := `SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Laman.PlanarLaman.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ _ G => ∃ H, H ≤ G ∧ H.IsLaman) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Laman.PlanarLaman
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev converseArena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
    (_h : G.IsGenericallyRigid 2) (_hV : 2 ≤ Fintype.card V), R.readout () V G

abbrev converseScope := type_of% (@SimpleGraph.IsGenericallyRigid.exists_isLaman_le.{u})

private theorem converse_bridge :
    converseScope.{u} ↔ (converseArena.{u}).Law actual.{u} := Iff.rfl

private theorem rejected_converse : ¬ (converseArena.{u}).Law rejected.{u} := by
  intro h
  exact h (G := (⊤ : SimpleGraph (ULift.{u} (Fin 2)))) base_rigid (by norm_num)

def converseFamilyRegistration :
    DependentFamily.Registration converseArena.{u} converseScope.{u} where
  actual := actual.{u}
  bridge := converse_bridge.{u}
  variation := ⟨@SimpleGraph.IsGenericallyRigid.exists_isLaman_le.{u},
    rejected.{u}, rejected_converse.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u}, ?_, rfl, rejected_converse.{u}⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := familyRegistration.dependence

noncomputable def converseRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@SimpleGraph.IsGenericallyRigid.exists_isLaman_le.{u})
      (DependentFamily.Realization signature.{u}) (Type u) Unit where
  unitName := `SimpleGraph.IsGenericallyRigid.exists_isLaman_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Laman.PlanarLaman.converseFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨converseArena.{u}⟩
  objectArena := .source ⟨converseArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source converseArena.{u} ⟨converseFamilyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ _ G => ∃ H, H ≤ G ∧ H.IsLaman) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Laman.PlanarLaman
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Combinatorics.Graph.Laman.PlanarLaman
