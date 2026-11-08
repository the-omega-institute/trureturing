import D5.S3.Combinatorics.Graph.Laman.History
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! # Source-bound history observation over every graph carrier -/

namespace Reg.D5.S3.Combinatorics.Graph.Laman.History

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open SimpleGraph SimpleGraph.Henneberg

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
  DependentFamily.realize signature.{u} (fun _ _ G => HasHistory G) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    (G.edgeSet.ncard + 3 = 2 * Nat.card V ∧
      ∀ S : Set V, 2 ≤ S.ncard → (G.induce S).edgeSet.ncard + 3 ≤ 2 * S.ncard) ↔
    R.readout () V G

abbrev sourceScope := type_of% (@laman_iff_history.{u})

private theorem source_bridge : sourceScope.{u} ↔ (arena.{u}).Law actual.{u} := Iff.rfl

private theorem base_history : HasHistory (⊤ : SimpleGraph (ULift.{u} (Fin 2))) := by
  refine ⟨[], .singleton _, ?_⟩
  exact ⟨Iso.completeGraph Equiv.ulift⟩

private theorem bot_not_history : ¬ HasHistory (⊥ : SimpleGraph (ULift.{u} (Fin 2))) := by
  intro h
  have hc := ((laman_iff_history _).mpr h).1
  norm_num at hc

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ (arena.{u}).Law rejected.{u} := by
  intro h
  exact (h (⊤ : SimpleGraph (ULift.{u} (Fin 2)))).mp
    ((laman_iff_history (⊤ : SimpleGraph (ULift.{u} (Fin 2)))).mpr base_history)

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
  actual := actual.{u}
  bridge := source_bridge.{u}
  variation := ⟨@laman_iff_history.{u}, rejected.{u}, rejected_law.{u}⟩
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
    change HasHistory (⊤ : SimpleGraph (ULift.{u} (Fin 2))) ≠
      HasHistory (⊥ : SimpleGraph (ULift.{u} (Fin 2)))
    intro he
    exact bot_not_history (he ▸ base_history)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@laman_iff_history.{u}) (DependentFamily.Realization signature.{u}) (Type u) Unit where
  unitName := `SimpleGraph.Henneberg.laman_iff_history.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Laman.History.familyRegistration
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
    (fun _ _ G => HasHistory G) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Laman.History
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Laman.History
