/- GID: D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeWorld/WorldDomains
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dependent world domains, explicit guards, and typed selection images. -/

import D5.S3.ConceptDynamics.Spacetime.ComplementCharge
import Mathlib.Data.Set.Restrict

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeWorld.WorldDomains

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Spacetime.ComplementCharge

abbrev Valuation {S : Type*} (V : S → Type*) := (s : S) → V s

/-- Nonempty coordinates do not assert compatibility of arbitrary joint constraints. -/
structure JointDomain {S : Type*} (V : S → Type*) where
  coordinate_nonempty : ∀ s, Nonempty (V s)
  allowed : Set (Valuation V)
  nonempty : allowed.Nonempty

abbrev JointDomain.World {S : Type*} {V : S → Type*} (D : JointDomain V) := ↥D.allowed

instance worldNonempty {S : Type*} {V : S → Type*} (D : JointDomain V) :
    Nonempty D.World := D.nonempty.to_subtype

/-- All occurrences of a coordinate are read from this same world argument. -/
def coordinate {S : Type*} {V : S → Type*} (D : JointDomain V) (s : S)
    (world : D.World) : V s := world.val s

variable {S : Type*} {V : S → Type*}

/-- The restricted domain remains a subset of the original dependent product. -/
def guardedDomain (D : JointDomain V) (guard : D.World → Prop) : Set (Valuation V) :=
  {v | ∃ hv : v ∈ D.allowed, guard ⟨v, hv⟩}

/-- A legal input has both the original membership proof and its guard proof. -/
noncomputable def guardedWorldEquiv (D : JointDomain V) (guard : D.World → Prop) :
    ↥(guardedDomain D guard) ≃ {w : D.World // guard w} where
  toFun w := ⟨⟨w.val, w.property.choose⟩, w.property.choose_spec⟩
  invFun w := ⟨w.val.val, w.val.property, w.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

theorem guarded_nonempty_iff (D : JointDomain V) (guard : D.World → Prop) :
    (guardedDomain D guard).Nonempty ↔ ∃ w : D.World, guard w := by
  constructor
  · rintro ⟨v, hv, hg⟩
    exact ⟨⟨v, hv⟩, hg⟩
  · rintro ⟨w, hg⟩
    exact ⟨w.val, w.property, hg⟩

def restrictGuard (D : JointDomain V) (guard : D.World → Prop)
    (satisfiable : ∃ w : D.World, guard w) : JointDomain V where
  coordinate_nonempty := D.coordinate_nonempty
  allowed := guardedDomain D guard
  nonempty := (guarded_nonempty_iff D guard).mpr satisfiable

/-- Evaluation accepts only legal worlds; it specifies no value outside the guard. -/
noncomputable def guardedEval {T : Type*} (D : JointDomain V) (guard : D.World → Prop)
    (operation : {w : D.World // guard w} → T) : ↥(guardedDomain D guard) → T :=
  operation ∘ guardedWorldEquiv D guard

/-- World exclusion lives in the valuation product, not in the event selection type. -/
def worldExclusion (D : JointDomain V) (excluded : Set D.World) : Set (Valuation V) :=
  Subtype.val '' excludedᶜ

theorem world_exclusion_eq_guarded (D : JointDomain V) (excluded : Set D.World) :
    worldExclusion D excluded = guardedDomain D (fun w => w ∉ excluded) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hv, hg⟩
    exact ⟨⟨v, hv⟩, hg, rfl⟩

/-- Exclude entire possible selections, as elements of the native selection space. -/
def selectionFamilyExclusion {d : Nat} {C : Context d}
    (K : Set (Selection C)) : Set (Selection C) := Kᶜ

/-- Apply native contribution complement separately to each possible selection. -/
def complementFamily {d : Nat} {C : Context d}
    (K : Set (Selection C)) : Set (Selection C) := complement '' K

def possibleReadouts {d : Nat} {C : Context d} (K : Set (Selection C)) : Set Int :=
  (fun A => q ⟨C, A⟩) '' K

/-- This is the image of pointwise event complement, not exclusion of a family. -/
theorem complement_family_readouts {d : Nat} {C : Context d} (K : Set (Selection C)) :
    possibleReadouts (complementFamily K) =
      (fun z => background C - z) '' possibleReadouts K := by
  simp only [possibleReadouts, complementFamily, Set.image_image]
  congr 1
  funext A
  exact complement_readout A

/-- A shared fixed context may choose a different native selection in each world. -/
def selectionState {d : Nat} (D : JointDomain V) (C : Context d)
    (A : D.World → Selection C) : D.World → Rich d := fun w => ⟨C, A w⟩

/-- Incompatible constraints and a zero-valued compatible model have different images. -/
theorem incompatible_image_ne_zero (D : JointDomain V) :
    (fun _ : Valuation V => (0 : Int)) '' (∅ : Set (Valuation V)) = ∅ ∧
      (fun _ : Valuation V => (0 : Int)) '' D.allowed = {0} ∧
      (fun _ : Valuation V => (0 : Int)) '' (∅ : Set (Valuation V)) ≠
        (fun _ : Valuation V => (0 : Int)) '' D.allowed := by
  rw [Set.image_empty, D.nonempty.image_const]
  simp

end D5.S3.ConceptDynamics.SpacetimeWorld.WorldDomains
