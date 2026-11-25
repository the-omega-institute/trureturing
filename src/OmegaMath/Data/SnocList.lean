/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Finite lists with an append-at-the-end constructor.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- A finite list built by appending one element at a time. -/
inductive SnocList (A : Type u) where
  | empty
  | extend (initial : SnocList A) (last : True → A)

namespace SnocList

/-- Append a final element. -/
def pushBack {A : Type u} (initial : SnocList A) (last : A) : SnocList A :=
  .extend initial (fun _ => last)


/-- Apply a function to each element in insertion order. -/
def map {A : Type u} {B : Type v} (f : A → B) : SnocList A → SnocList B :=
  SnocList.rec (motive := fun _ => SnocList B) .empty
    (fun _ last initial => initial.pushBack (f (last True.intro)))

/-- Membership in a list built by appending elements. -/
def Mem {A : Type u} (value : A) : SnocList A → Prop :=
  SnocList.rec (motive := fun _ => Prop) False
    (fun _ last earlier => Or earlier (Eq (last True.intro) value))

/-- A member of a mapped list has a preimage in the original list. -/
theorem exists_of_mem_map {A : Type u} {B : Type v} (f : A → B)
    (values : SnocList A) (value : B) (member : Mem value (map f values)) :
    Exists (fun original => And (Mem original values) (Eq (f original) value)) :=
  (SnocList.rec (motive := fun values => Mem value (map f values) →
    Exists (fun original => And (Mem original values) (Eq (f original) value)))
    (fun noMember => False.elim noMember)
    (fun _ last earlier belongs => belongs.elim
      (fun inPrefix => (earlier inPrefix).elim (fun original found =>
        Exists.intro original (And.intro (Or.inl found.left) found.right)))
      (fun equalsLast =>
        Exists.intro (last True.intro) (And.intro (Or.inr Eq.refl) equalsLast))) values) member

end SnocList
end Omega
