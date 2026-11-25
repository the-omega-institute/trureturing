/- GID: D5/S0/CategoryTheory/Naturality
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Category and functor operations with separate law predicates. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Category and functor operations with separate law predicates. Naturality is
pointwise equality of the two composites around each square.
-/

@[expose] public section

namespace Omega.CategoryTheory

/-- Identities and composition on a family of arrow types. -/
structure Category (Obj : Type u) (Arrow : Obj → Obj → Type v) where
  id : ∀ X : Obj, Arrow X X
  comp : ∀ {X Y Z : Obj}, Arrow X Y → Arrow Y Z → Arrow X Z

/-- Left and right identity and associativity for the category operations. -/
def Category.Laws {Obj : Type u} {Arrow : Obj → Obj → Type v} (C : Category Obj Arrow) : Prop :=
  And (∀ {X Y : Obj} (f : Arrow X Y), Eq (C.comp (C.id X) f) f)
    (And (∀ {X Y : Obj} (f : Arrow X Y), Eq (C.comp f (C.id Y)) f)
      (∀ {W X Y Z : Obj} (f : Arrow W X) (g : Arrow X Y) (h : Arrow Y Z),
        Eq (C.comp (C.comp f g) h) (C.comp f (C.comp g h))))

/-- Actions on objects and arrows between two categories. -/
structure Functor {ObjC : Type u} {ObjD : Type v}
    (ArrowC : ObjC → ObjC → Type w) (ArrowD : ObjD → ObjD → Type z) where
  obj : ObjC → ObjD
  map : ∀ {X Y : ObjC}, ArrowC X Y → ArrowD (obj X) (obj Y)

/-- A functor preserves identities and composition. -/
def Functor.Laws {ObjC : Type u} {ObjD : Type v}
    {ArrowC : ObjC → ObjC → Type w} {ArrowD : ObjD → ObjD → Type z}
    (F : Functor ArrowC ArrowD) (C : Category ObjC ArrowC) (D : Category ObjD ArrowD) : Prop :=
  And (∀ X : ObjC, Eq (F.map (C.id X)) (D.id (F.obj X)))
    (∀ {X Y Z : ObjC} (f : ArrowC X Y) (g : ArrowC Y Z),
      Eq (F.map (C.comp f g)) (D.comp (F.map f) (F.map g)))

/-- Components of a transformation between two functors on the same categories. -/
abbrev Transformation {ObjC : Type u} {ObjD : Type v}
    {ArrowC : ObjC → ObjC → Type w} {ArrowD : ObjD → ObjD → Type z}
    (F G : Functor ArrowC ArrowD) := ∀ X : ObjC, ArrowD (F.obj X) (G.obj X)

/-- The transformation commutes with the functors on each arrow. -/
def Transformation.IsNatural {ObjC : Type u} {ObjD : Type v}
    {ArrowC : ObjC → ObjC → Type w} {ArrowD : ObjD → ObjD → Type z}
    {F G : Functor ArrowC ArrowD}
    (app : Transformation F G) (D : Category ObjD ArrowD) : Prop :=
  ∀ {X Y : ObjC} (f : ArrowC X Y), Eq (D.comp (F.map f) (app Y)) (D.comp (app X) (G.map f))

end Omega.CategoryTheory
