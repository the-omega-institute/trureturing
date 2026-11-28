import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.Logic.Relation
import Mathlib.Order.Hom.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.WithBot

/-!
# Two-row extension of a fence of order maps

Each comparison step adds a lower and a middle copy of the domain to the
previous extension. The lower copy moves up to the middle copy, and both
copies then move down to the embedded domain in the previous extension.
-/

set_option autoImplicit false

namespace D5.S3.Topology.TwoRowFenceCylinder

open Relation (EqvGen)

universe u w

variable {R V : Type u} [PartialOrder R] [PartialOrder V]
variable {P : Type w} [Preorder P]

private inductive Rows (e : R ↪o V)
  | lower (r : R)
  | middle (r : R)
  | old (v : V)

-- For an embedding with lower range, `v ≤ e s` means `v = e r` for some `r ≤ s`.
private def rowLE (e : R ↪o V) : Rows e → Rows e → Prop
  | .lower r, .lower s => r ≤ s
  | .lower r, .middle s => r ≤ s
  | .middle r, .middle s => r ≤ s
  | .old v, .old w => v ≤ w
  | .old v, .middle s => v ≤ e s
  | _, _ => False

private instance (e : R ↪o V) : PartialOrder (Rows e) where
  le := rowLE e
  le_refl x := by
    cases x with
    | lower r => exact le_refl r
    | middle r => exact le_refl r
    | old v => exact le_refl v
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;> first
    | exact False.elim hxy
    | exact False.elim hyz
    | exact le_trans (α := R) hxy hyz
    | exact le_trans (α := V) hxy hyz
    | exact le_trans (α := V) hxy (e.monotone hyz)
  le_antisymm x y hxy hyx := by
    cases x <;> cases y <;> first
    | exact False.elim hxy
    | exact False.elim hyx
    | exact congrArg Rows.lower (le_antisymm (α := R) hxy hyx)
    | exact congrArg Rows.middle (le_antisymm (α := R) hxy hyx)
    | exact congrArg Rows.old (le_antisymm (α := V) hxy hyx)

private instance [Finite R] [Finite V] (e : R ↪o V) : Finite (Rows e) :=
  Finite.of_surjective
    (Sum.elim Rows.lower (Sum.elim Rows.middle Rows.old) : R ⊕ (R ⊕ V) → Rows e)
    (by
      intro x
      cases x with
      | lower r => exact ⟨Sum.inl r, rfl⟩
      | middle r => exact ⟨Sum.inr (Sum.inl r), rfl⟩
      | old v => exact ⟨Sum.inr (Sum.inr v), rfl⟩)

private def lowerEmbedding (e : R ↪o V) : R ↪o Rows e :=
  OrderEmbedding.ofMapLEIff Rows.lower (fun _ _ => Iff.rfl)

private theorem lowerRange (e : R ↪o V) :
    IsLowerSet (Set.range (lowerEmbedding e : R → Rows e)) := by
  rintro _ x hxy ⟨r, rfl⟩
  cases x with
  | lower s => exact ⟨s, rfl⟩
  | middle s => exact False.elim hxy
  | old v => exact False.elim hxy

private def includeOld (e : R ↪o V) : V →o Rows e :=
  ⟨Rows.old, fun _ _ h => h⟩

private def raise (e : R ↪o V) : Rows e →o Rows e where
  toFun
    | .lower r => .middle r
    | .middle r => .middle r
    | .old v => .old v
  monotone' := by
    intro x y hxy
    cases x <;> cases y <;> first | exact False.elim hxy | exact hxy

private def project (e : R ↪o V) : Rows e →o V where
  toFun
    | .lower r => e r
    | .middle r => e r
    | .old v => v
  monotone' := by
    intro x y hxy
    cases x <;> cases y <;> first
    | exact False.elim hxy
    | exact hxy
    | exact e.monotone hxy

private theorem id_le_raise (e : R ↪o V) : OrderHom.id ≤ raise e := by
  intro x
  cases x with
  | lower r => exact le_refl r
  | middle r => exact le_refl r
  | old v => exact le_refl v

private theorem project_le_raise (e : R ↪o V) :
    (includeOld e).comp (project e) ≤ raise e := by
  intro x
  cases x with
  | lower r => exact le_refl (e r)
  | middle r => exact le_refl (e r)
  | old v => exact le_refl v

private theorem mapFence {X Y : Type*} [Preorder X] [Preorder Y] (F : X → Y)
    (hF : Monotone F) {x y : X} (h : EqvGen (· ≤ ·) x y) :
    EqvGen (· ≤ ·) (F x) (F y) := by
  induction h with
  | rel a b hab => exact .rel _ _ (hF hab)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem contractRows (e : R ↪o V) {c : V}
    (hc : EqvGen (· ≤ ·) (OrderHom.id : V →o V) (OrderHom.const V c)) :
    EqvGen (· ≤ ·) (OrderHom.id : Rows e →o Rows e) (OrderHom.const (Rows e) (Rows.old c)) := by
  let lift (k : V →o V) : Rows e →o Rows e := (includeOld e).comp (k.comp (project e))
  have lift_mono : Monotone lift := by
    intro a b hab x
    exact (includeOld e).monotone (hab (project e x))
  have tail : EqvGen (· ≤ ·) ((includeOld e).comp (project e))
      (OrderHom.const (Rows e) (Rows.old c)) := mapFence lift lift_mono hc
  exact .trans _ _ _ (.rel _ _ (id_le_raise e))
    (.trans _ _ _ (.symm _ _ (.rel _ _ (project_le_raise e))) tail)

private def evaluate (e : R ↪o V) (ev : V →o P) {f g h : R →o P}
    (hf : f ≤ h) (hg : g ≤ h) (agree : ev.comp e.toOrderHom = g) : Rows e →o P where
  toFun
    | .lower r => f r
    | .middle r => h r
    | .old v => ev v
  monotone' := by
    intro x y hxy
    cases x with
    | lower r =>
      cases y with
      | lower s => exact f.monotone hxy
      | middle s => exact (hf r).trans (h.monotone hxy)
      | old v => exact False.elim hxy
    | middle r =>
      cases y with
      | lower s => exact False.elim hxy
      | middle s => exact h.monotone hxy
      | old v => exact False.elim hxy
    | old v =>
      cases y with
      | lower s => exact False.elim hxy
      | middle s =>
        change ev v ≤ h s
        calc
          ev v ≤ ev (e s) := ev.monotone (show v ≤ e s from hxy)
          _ = g s := congrArg (fun k : R →o P => k s) agree
          _ ≤ h s := hg s
      | old w => exact ev.monotone hxy

/-- An exact extension across a lower embedding into a finite poset whose
identity lies in the pointwise comparison class of a constant. -/
def HasExtension (g : R →o P) : Prop :=
  ∃ (V : Type u) (order : PartialOrder V) (_ : Finite V),
    letI : PartialOrder V := order
    ∃ (e : R ↪o V) (ev : V →o P),
      IsLowerSet (Set.range (e : R → V)) ∧ ev.comp e.toOrderHom = g ∧
        ∃ c : V, EqvGen (· ≤ ·) (OrderHom.id : V →o V) (OrderHom.const V c)

private theorem prepend [Finite R] {f g h : R →o P} (hf : f ≤ h) (hg : g ≤ h)
    (ext : HasExtension g) : HasExtension f := by
  obtain ⟨V, orderV, finiteV, data⟩ := ext
  let _ : PartialOrder V := orderV
  let _ : Finite V := finiteV
  obtain ⟨e, ev, _, agree, c, hc⟩ := data
  exact ⟨Rows e, inferInstance, inferInstance, lowerEmbedding e, evaluate e ev hf hg agree,
    lowerRange e, rfl, Rows.old c, contractRows e hc⟩

private theorem const_hasExtension [Finite R] (p : P) :
    HasExtension (OrderHom.const R p) := by
  let e : R ↪o WithTop R :=
    OrderEmbedding.ofMapLEIff (fun r : R => (r : WithTop R)) (fun _ _ => WithTop.coe_le_coe)
  have hlower : IsLowerSet (Set.range (e : R → WithTop R)) := by
    rintro _ a hxy ⟨r, rfl⟩
    change a ≤ (r : WithTop R) at hxy
    cases a with
    | top => exact (WithTop.not_top_le_coe r hxy).elim
    | coe s => exact ⟨s, rfl⟩
  refine ⟨WithTop R, inferInstance, inferInstance, e, OrderHom.const (WithTop R) p,
    hlower, rfl, ⊤, .rel _ _ ?_⟩
  exact fun x => le_top (a := x)

private theorem hasExtension_iff_of_fence [Finite R] {f g : R →o P}
    (hfg : EqvGen (· ≤ ·) f g) : HasExtension f ↔ HasExtension g := by
  induction hfg with
  | rel f g hfg => exact ⟨prepend le_rfl hfg, prepend hfg le_rfl⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A fence from `g` to a constant yields a finite extension in the same
universe as `R`, with lower range and a fence from its identity to a constant. -/
theorem exists_extension_of_eqvGen [Finite R] {g : R →o P} {p : P}
    (hg : EqvGen (· ≤ ·) g (OrderHom.const R p)) : HasExtension g :=
  (hasExtension_iff_of_fence hg).mpr (const_hasExtension p)

end D5.S3.Topology.TwoRowFenceCylinder
