/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega.Option

protected def elim {α : Type u} {β : Sort v} : Option α → β → (α → β) → β :=
  fun x fallback f => Option.casesOn (motive := fun _ => β) x fallback f

protected def bind {α : Type u} {β : Type v} : Option α → (α → Option β) → Option β :=
  fun x f => Option.casesOn (motive := fun _ => Option β) x none f

def join {α : Type u} (x : Option (Option α)) : Option α := Option.bind x id

protected def orElse {α : Type u} : Option α → (Unit → Option α) → Option α :=
  fun x fallback => Option.casesOn (motive := fun _ => Option α) x (fallback Unit.unit) some

def or {α : Type u} : Option α → Option α → Option α :=
  fun x y => Option.casesOn (motive := fun _ => Option α) x y some

def merge {α : Type u} (fn : α → α → α) : Option α → Option α → Option α :=
  fun x y => Option.casesOn (motive := fun _ => Option α) x
    (Option.casesOn (motive := fun _ => Option α) y none some)
    (fun a => Option.casesOn (motive := fun _ => Option α) y (some a) (fun b => some (fn a b)))

protected def tryCatch {α : Type u} (x : Option α) (handle : Unit → Option α) : Option α :=
  Option.casesOn (motive := fun _ => Option α) x (handle Unit.unit) (fun _ => x)

def isNone {α : Type u} : Option α → Bool :=
  fun x => Option.casesOn (motive := fun _ => Bool) x Bool.true (fun _ => Bool.false)

def isSome {α : Type u} : Option α → Bool :=
  fun x => Option.casesOn (motive := fun _ => Bool) x Bool.false (fun _ => Bool.true)

protected def any {α : Type u} (p : α → Bool) : Option α → Bool :=
  fun x => Option.casesOn (motive := fun _ => Bool) x Bool.false p

protected def all {α : Type u} (p : α → Bool) : Option α → Bool :=
  fun x => Option.casesOn (motive := fun _ => Bool) x Bool.true p

protected def le {α : Type u} {β : Type v} (r : α → β → Prop) : Option α → Option β → Prop :=
  fun x y => Option.casesOn (motive := fun _ => Prop) x
    (Option.casesOn (motive := fun _ => Prop) y True (fun _ => True))
    (fun a => Option.casesOn (motive := fun _ => Prop) y False (r a))

protected def lt {α : Type u} {β : Type v} (r : α → β → Prop) : Option α → Option β → Prop :=
  fun x y => Option.casesOn (motive := fun _ => Prop) x
    (Option.casesOn (motive := fun _ => Prop) y False (fun _ => True))
    (fun a => Option.casesOn (motive := fun _ => Prop) y False (r a))

def toList {α : Type u} : Option α → List α :=
  fun x => Option.casesOn (motive := fun _ => List α) x List.nil (fun a => List.cons a List.nil)

theorem all_none :
    Eq (Option.all p Option.none) Bool.true := Omega.rfl

theorem all_some :
    Eq (Option.all p (Option.some x)) (p x) := Omega.rfl

theorem any_none :
    Eq (Option.any p Option.none) Bool.false := Omega.rfl

theorem any_some :
    Eq (Option.any p (Option.some x)) (p x) := Omega.rfl

theorem bind_none {α : Type u} {β : Type v} (f : α → Option β) :
    Eq (Option.bind Option.none f) Option.none := Omega.rfl

theorem bind_some {α : Type u} {β : Type v} (a : α) (f : α → Option β) :
    Eq (Option.bind (Option.some a) f) (f a) := Omega.rfl

theorem getD_none :
    Eq (Option.getD Option.none a) a := Omega.rfl

theorem getD_some :
    Eq (Option.getD (Option.some a) b) a := Omega.rfl

theorem isNone_none {α : Type u} :
    Eq (Option.isNone (Option.none : Option α)) Bool.true := Omega.rfl

theorem isNone_some :
    Eq (Option.isNone (Option.some a)) Bool.false := Omega.rfl

theorem isSome_none {α : Type u} :
    Eq (Option.isSome (Option.none : Option α)) Bool.false := Omega.rfl

theorem isSome_some :
    Eq (Option.isSome (Option.some a)) Bool.true := Omega.rfl

theorem join_none {α : Type u} :
    Eq (Option.join (Option.none : Option (Option α))) Option.none := Omega.rfl

theorem join_some :
    Eq (Option.join (Option.some o)) o := Omega.rfl

theorem map_none {α : Type u} {β : Type v} (f : α → β) :
    Eq (Option.map f Option.none) Option.none := Omega.rfl

theorem map_some {α : Type u} {β : Type v} (a : α) (f : α → β) :
    Eq (Option.map f (Option.some a)) (Option.some (f a)) := Omega.rfl

theorem orElse_none :
    Eq (Option.orElse Option.none b) (b Unit.unit) := Omega.rfl

theorem orElse_some :
    Eq (Option.orElse (Option.some a) b) (Option.some a) := Omega.rfl

end Omega.Option
