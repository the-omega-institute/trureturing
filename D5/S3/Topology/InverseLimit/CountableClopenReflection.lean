/- GID: D5/S3/Topology/InverseLimit/CountableClopenReflection
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/CountableClopenReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Countably many final clopens descend together below omega-one. -/

import D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Countable common-stage reflection in profinite inverse limits

The countable family is reflected into one actual component of an
omega-one-indexed inverse system. The common component remains strictly
below omega-one and may be chosen above a prescribed stage. Surjectivity
of actual limit projections preserves nonemptiness and disjointness.

This is known inverse-limit background used by a transfinite compactum
construction. It does not construct that compactum or settle a CH question.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Set Function
open scoped Ordinal

namespace D5.S3.Topology.InverseLimit.CountableClopenReflection

universe u v

/-- The proper stages of an omega-one-length construction. -/
abbrev CountableStage := Set.Iio (ω₁ : Ordinal.{0})

private instance : Nonempty CountableStage :=
  ⟨⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩⟩

/-- A consumed application of the existing full-thread lifting theorem. -/
private theorem projection_surjective {J : Type v} [SmallCategory J]
    [IsCofiltered J] [Quiver.IsThin J] (F : J ⥤ Profinite.{max u v})
    [∀ j, Nonempty (F.obj j)] (C : Cone F) (hC : IsLimit C)
    (hs : ∀ {i j} (f : i ⟶ j), Surjective (F.map f)) (i : J) :
    Surjective (C.π.app i) := by
  intro a
  let T := F ⋙ Profinite.toTopCat
  let : ∀ j, Nonempty (T.obj j) := fun j => inferInstanceAs (Nonempty (F.obj j))
  let : ∀ j, CompactSpace (T.obj j) := fun j => inferInstanceAs (CompactSpace (F.obj j))
  let : ∀ j, T2Space (T.obj j) := fun j => inferInstanceAs (T2Space (F.obj j))
  have ha : a ∈ range ((TopCat.limitCone T).π.app i) := by
    rw [D5.S1.Dynamics.Shadowing.compact_projection_image T i]
    exact (Functor.mem_eventualRange_iff _).2 fun j f => hs f a
  obtain ⟨x, hx⟩ := ha
  let e := hC.conePointUniqueUpToIso (Profinite.limitConeIsLimit F)
  refine ⟨e.inv x, ?_⟩
  have he := ConcreteCategory.congr_hom
    (hC.conePointUniqueUpToIso_inv_comp (Profinite.limitConeIsLimit F) i) x
  exact he.trans hx

/-- A countable family of final clopens has simultaneous exact clopen traces
at one proper stage above a requested base. Nonemptiness and disjointness
are equivalent at the final and stage levels, including empty clopens. -/
theorem exists_common_stage {ι : Type u} [Countable ι] (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    [∀ j, Nonempty (F.obj j)] (C : Cone F) (hC : IsLimit C)
    (hs : ∀ {i j} (f : i ⟶ j), Surjective (F.map f))
    (base : CountableStage) (W : ι → Set C.pt) (hW : ∀ n, IsClopen (W n)) :
    ∃ β : CountableStage, base ≤ β ∧
      ∃ V : ι → Set (F.obj (op β)),
        (∀ n, IsClopen (V n)) ∧
        (∀ n, W n = C.π.app (op β) ⁻¹' V n) ∧
        (∀ n, (V n).Nonempty ↔ (W n).Nonempty) ∧
        (∀ m n, Disjoint (V m) (V n) ↔ Disjoint (W m) (W n)) := by
  classical
  choose j U hU hWU using fun n =>
    Profinite.exists_isClopen_of_cofiltered.{0, 1} C hC (hW n)
  let b : Option ι → Ordinal.{0} := fun i => i.elim base.1 (fun n => (j n).unop.1)
  have hb : ∀ i, b i < ω₁ := by
    intro i
    cases i with
    | none => exact base.2
    | some n => exact (j n).unop.2
  let β : CountableStage := ⟨⨆ n, b n, Ordinal.iSup_lt_omega_one hb⟩
  have hbase : base ≤ β := Ordinal.le_iSup b none
  have hj : ∀ n, (j n).unop ≤ β := fun n => Ordinal.le_iSup b (some n)
  let q : ∀ n, op β ⟶ j n := fun n => (homOfLE (hj n)).op
  let V : ι → Set (F.obj (op β)) := fun n => F.map (q n) ⁻¹' U n
  have hV : ∀ n, IsClopen (V n) := fun n =>
    (hU n).preimage (F.map (q n)).hom.hom.continuous
  have hWV : ∀ n, W n = C.π.app (op β) ⁻¹' V n := by
    intro n
    rw [hWU n]
    ext x
    have h := ConcreteCategory.congr_hom (C.w (q n)) x
    change (C.π.app (j n) x ∈ U n) ↔ (F.map (q n) (C.π.app (op β) x) ∈ U n)
    exact h ▸ Iff.rfl
  have hp := projection_surjective.{0, 1} F C hC hs (op β)
  refine ⟨β, hbase, V, hV, hWV, ?_, ?_⟩
  · intro n
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨x, hx⟩ := hp a
      refine ⟨x, ?_⟩
      rw [hWV n]
      change C.π.app (op β) x ∈ V n
      rwa [hx]
    · rintro ⟨x, hx⟩
      refine ⟨C.π.app (op β) x, ?_⟩
      rw [hWV n] at hx
      exact hx
  · intro m n
    constructor
    · intro h
      apply Set.disjoint_left.mpr
      intro x hx hy
      rw [hWV m] at hx
      rw [hWV n] at hy
      exact Set.disjoint_left.mp h hx hy
    · intro h
      apply Set.disjoint_left.mpr
      intro a ha hb
      obtain ⟨x, hx⟩ := hp a
      have hxm : x ∈ W m := by
        rw [hWV m]
        change C.π.app (op β) x ∈ V m
        rwa [hx]
      have hxn : x ∈ W n := by
        rw [hWV n]
        change C.π.app (op β) x ∈ V n
        rwa [hx]
      exact Set.disjoint_left.mp h hxm hxn

end D5.S3.Topology.InverseLimit.CountableClopenReflection
