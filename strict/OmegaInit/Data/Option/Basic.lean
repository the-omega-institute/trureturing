/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Control.Basic

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

def isSome {α : Type u} : Option α → Bool :=
  fun x => Option.casesOn (motive := fun _ => Bool) x Bool.false (fun _ => Bool.true)

@[no_expose] def isNone {α : Type u} : Option α → Bool := fun x => Bool.not (isSome x)

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

attribute [irreducible] isNone

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

port_definition instFunctorOption with_native_code
port_definition instMonadOption with_native_code
port_definition Option.instOrElse with_native_code
port_definition Option.instDecidableEq.match_1 with_native_code
port_definition Option.toArray with_native_code
port_definition Option.getM with_native_code
port_definition Option.mapM with_native_code
port_definition Option.mapA with_native_code
port_definition Option.elimM with_native_code
port_definition Option.isEqSome.match_1 with_native_code
port_definition Option.isEqSome with_native_code

port_definition Option.guard with_native_code
port_definition Option.isSome.match_1 with_native_code
port_definition Option.filter with_native_code
port_definition Option.getDM with_native_code
port_definition Option.bindM with_native_code
port_definition Option.sequence.match_1 with_native_code
port_definition Option.sequence with_native_code
port_definition Option.filterM.match_1 with_native_code
port_definition Option.filterM with_native_code
port_definition Option.min.match_1 with_native_code
port_definition Option.min with_native_code
port_definition Option.max with_native_code
port_definition Option.instMin with_native_code
port_definition Option.instMax with_native_code
port_definition Option.instBEq.beq.match_1 with_native_code
port_definition Option.instBEq.beq with_native_code
port_definition Option.instBEq with_native_code
port_definition instMonadExceptOfUnitOption with_native_code
port_definition instAlternativeOption with_native_code
port_definition liftOption with_native_code

port_definition instLEOption with_native_code
port_definition instLTOption with_native_code
port_proof Option.instDecidableEq._proof_1 by_reflexivity
port_proof Option.instDecidableEq._proof_2
port_proof Option.instDecidableEq._proof_3
port_definition Option.decidableNoneEq with_native_code
port_definition Option.decidableEqNone with_native_code
port_proof Option.instDecidableEq._proof_4
port_proof Option.instDecidableEq._proof_5
port_definition Option.instDecidableEq.match_3 with_native_code
port_definition Option.instDecidableEq with_native_code
port_definition Option.instDecidableRelLt.match_1 with_native_code
port_definition Option.instDecidableRelLt with_native_code
port_definition Option.instDecidableRelLe with_native_code

end
end

namespace Omega.Option

@[expose, implicit_reducible] public def get {α : Type u} :
    (o : Option α) → Eq o.isSome Bool.true → α :=
  fun o h => Option.casesOn (motive := fun t => Eq t.isSome Bool.true → α) o
    (fun impossible => False.elim (Bool.decEq._proof_1 Bool.false Bool.true impossible)) (fun value _ => value) h

end Omega.Option
