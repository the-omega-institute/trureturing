import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.CosetActions.FixedCosetBranching
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ZMod.Basic

/-! Observe the existence and cardinality of fixed left cosets as the acting
element varies with the ambient group and subgroup held fixed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.FiniteGroups.CosetActions.FixedCosetBranching

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.CosetActions.FixedCosetBranching

noncomputable section
universe u

structure GroupData where
  G : Type u
  groupG : Group G
  K : @Subgroup G groupG

private abbrev Two := ULift.{u} (Multiplicative (ZMod 2))

private def other : Two.{u} := ULift.up (Multiplicative.ofAdd 1)

private theorem other_ne_one : (other : Two.{u}) ≠ 1 := by
  intro h
  have h' := congrArg (fun a : Two.{u} => Multiplicative.toAdd a.down) h
  change (1 : ZMod 2) = 0 at h'
  exact one_ne_zero h'

private theorem fixedAtOne {G : Type u} [Group G] (K : Subgroup G) :
    Nonempty (FixedCosets K 1) :=
  (fixedCosets_nonempty_iff K 1).mpr ⟨1, ConjClasses.mem_carrier_mk, K.one_mem⟩

private theorem noFixedAtBot {G : Type u} [Group G] {g : G} (hg : g ≠ 1) :
    ¬ Nonempty (FixedCosets (⊥ : Subgroup G) g) := by
  intro h
  obtain ⟨x, hx⟩ := (fixedCosets_nonempty_iff (⊥ : Subgroup G) g).mp h
  have hx1 : x = 1 := Subgroup.mem_bot.mp hx.2
  have hconj : IsConj g x := hx.1
  exact hg (isConj_one_left.mp (hx1 ▸ hconj))

namespace Support

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature GroupData.{u} (fun p => p.G) (fun _ => Prop)

def actual : Realization signature.{u} :=
  realize signature (fun _ p g => by letI := p.groupG; exact Nonempty (FixedCosets p.K g))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {G : Type u} [groupG : Group G] (K : Subgroup G) (g : G),
    r.readout () ⟨G, groupG, K⟩ g ↔ ((ConjClasses.mk g).carrier ∩ (K : Set G)).Nonempty

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K : Subgroup Two.{u} := ⊥
  exact (h K 1).mpr ((fixedCosets_nonempty_iff K 1).mp (fixedAtOne K))

def sourceRegistration : Registration arena.{u} (type_of% (@fixedCosets_nonempty_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixedCosets_nonempty_iff.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro role
    let K : Subgroup Two.{u} := ⊥
    refine ⟨⟨Two.{u}, inferInstance, K⟩, 1, other, ?_⟩
    change Nonempty (FixedCosets K 1) ≠ Nonempty (FixedCosets K other)
    intro h
    exact noFixedAtBot other_ne_one (h ▸ fixedAtOne K)

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixedCosets_nonempty_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.FiniteGroups.CosetActions.FixedCosetBranching.fixedCosets_nonempty_iff.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.CosetActions.FixedCosetBranching.Support.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.CosetActions.FixedCosetBranching
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

namespace Count

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature GroupData.{u} (fun p => p.G) (fun _ => Nat)

def actual : Realization signature.{u} :=
  realize signature (fun _ p g => by letI := p.groupG; exact Nat.card (FixedCosets p.K g))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {G : Type u} [groupG : Group G] (K : Subgroup G) (g : G) [Finite G],
    r.readout () ⟨G, groupG, K⟩ g * Nat.card K =
      Nat.card (Subgroup.centralizer ({g} : Set G)) * Nat.card (ConjugatesIn K g)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K : Subgroup Two.{u} := ⊥
  have heq := (card_fixedCosets_mul_card_subgroup K 1).trans (h K 1).symm
  change Nat.card (FixedCosets K 1) * Nat.card K = 0 * Nat.card K at heq
  rw [Nat.zero_mul] at heq
  letI := fixedAtOne K
  exact (Nat.ne_of_gt (Nat.mul_pos Nat.card_pos Nat.card_pos)) heq

def sourceRegistration :
    Registration arena.{u} (type_of% (@card_fixedCosets_mul_card_subgroup.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@card_fixedCosets_mul_card_subgroup.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro role
    let K : Subgroup Two.{u} := ⊥
    refine ⟨⟨Two.{u}, inferInstance, K⟩, 1, other, ?_⟩
    change Nat.card (FixedCosets K 1) ≠ Nat.card (FixedCosets K other)
    have hzero : Nat.card (FixedCosets K other) = 0 :=
      Nat.card_eq_zero.mpr (Or.inl (not_nonempty_iff.mp (noFixedAtBot other_ne_one)))
    rw [hzero]
    letI := fixedAtOne K
    exact Nat.ne_of_gt Nat.card_pos

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@card_fixedCosets_mul_card_subgroup.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.FiniteGroups.CosetActions.FixedCosetBranching.card_fixedCosets_mul_card_subgroup.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.CosetActions.FixedCosetBranching.Count.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.CosetActions.FixedCosetBranching
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Count
end
end Reg.D5.S3.FiniteGroups.CosetActions.FixedCosetBranching
