import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation
universe u v
noncomputable section

abbrev signature : Signature where
  Params := Σ R : Type u, Σ G : Type v, CommRing R × Group G
  State p := letI := p.2.2.1; letI := p.2.2.2; Ideal (MonoidAlgebra p.1 p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.2.1; letI := p.2.2.2; Ideal (MonoidAlgebra p.1 p.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p I =>
    letI := p.2.2.1
    letI := p.2.2.2
    I ^ Nat.card p.2.1) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p _ =>
    letI := p.2.2.1
    letI := p.2.2.2
    ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {R : Type u} {G : Type v} [ring : CommRing R] [group : Group G]
    (p : ℕ) [Fact p.Prime] [CharP R p] [Finite G] (_hG : IsPGroup p G),
    r.readout () ⟨R, G, ring, group⟩
      (RingHom.ker (MonoidAlgebra.lift R R G (1 : G →* R)).toRingHom) = ⊥

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have he := h (R := ULift.{u} (ZMod 2)) (G := ULift.{v} Unit) 2
    (IsPGroup.of_subsingleton 2 _)
  exact top_ne_bot he

def family : Registration arena.{u,v}
    (type_of% @_root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation.augmentation_ideal_pow_card.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation.augmentation_ideal_pow_card.{u,v},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let p : signature.Params :=
      ⟨ULift.{u} (ZMod 2), ULift.{v} Unit, inferInstance, inferInstance⟩
    refine ⟨p, ⊤, ⊥, ?_⟩
    change (⊤ : Ideal (MonoidAlgebra (ULift.{u} (ZMod 2)) (ULift.{v} Unit))) ^
      Nat.card (ULift.{v} Unit) ≠ ⊥ ^ Nat.card (ULift.{v} Unit)
    simpa only [Nat.card_unique, Submodule.pow_one] using
      (top_ne_bot : (⊤ : Ideal (MonoidAlgebra (ULift.{u} (ZMod 2)) (ULift.{v} Unit))) ≠ ⊥)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation.augmentation_ideal_pow_card.{u,v})
    (type_of% actual.{u,v}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation.augmentation_ideal_pow_card.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation
