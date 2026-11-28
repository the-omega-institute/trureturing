/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
module
prelude
public import OmegaInit.Core
public import OmegaInit.PropLemmas

noncomputable section

@[expose] public section

namespace Omega.Sum

protected def elim {α : Type u} {β : Type v} {γ : Sort w} (f : α → γ) (g : β → γ) : Sum α β → γ :=
  fun x => Sum.casesOn (motive := fun _ => γ) x f g

protected def map {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
    (f : α → α') (g : β → β') : Sum α β → Sum α' β' :=
  Sum.elim (fun a => inl (f a)) (fun b => inr (g b))

def swap {α : Type u} {β : Type v} : Sum α β → Sum β α := Sum.elim inr inl

def isLeft {α : Type u} {β : Type v} : Sum α β → Bool :=
  fun x => Sum.casesOn (motive := fun _ => Bool) x (fun _ => Bool.true) (fun _ => Bool.false)

def isRight {α : Type u} {β : Type v} : Sum α β → Bool :=
  fun x => Sum.casesOn (motive := fun _ => Bool) x (fun _ => Bool.false) (fun _ => Bool.true)

def getLeft? {α : Type u} {β : Type v} : Sum α β → Option α :=
  fun x => Sum.casesOn (motive := fun _ => Option α) x Option.some (fun _ => Option.none)

def getRight? {α : Type u} {β : Type v} : Sum α β → Option β :=
  fun x => Sum.casesOn (motive := fun _ => Option β) x (fun _ => Option.none) Option.some

theorem elim_inl {α : Type u} {γ : Sort v} {β : Type w} (f : α → γ) (g : β → γ) (x : α) :
    Eq (Sum.elim f g (Sum.inl x)) (f x) := Omega.rfl

theorem elim_inr {α : Type u} {γ : Sort v} {β : Type w} (f : α → γ) (g : β → γ) (x : β) :
    Eq (Sum.elim f g (Sum.inr x)) (g x) := Omega.rfl

theorem getLeft?_inl {α : Type u} {β : Type v} {x : α} :
    Eq (Sum.getLeft? (Sum.inl x : Sum α β)) (Option.some x) := Omega.rfl

theorem getLeft?_inr {α : Type u} {β : Type v} {x : β} :
    Eq (Sum.getLeft? (Sum.inr x : Sum α β)) Option.none := Omega.rfl

theorem getRight?_inl {α : Type u} {β : Type v} {x : α} :
    Eq (Sum.getRight? (Sum.inl x : Sum α β)) Option.none := Omega.rfl

theorem getRight?_inr {α : Type u} {β : Type v} {x : β} :
    Eq (Sum.getRight? (Sum.inr x : Sum α β)) (Option.some x) := Omega.rfl

theorem isLeft_inl {α : Type u} {β : Type v} {x : α} :
    Eq (Sum.isLeft (Sum.inl x : Sum α β)) Bool.true := Omega.rfl

theorem isLeft_inr {α : Type u} {β : Type v} {x : β} :
    Eq (Sum.isLeft (Sum.inr x : Sum α β)) Bool.false := Omega.rfl

theorem isRight_inl {α : Type u} {β : Type v} {x : α} :
    Eq (Sum.isRight (Sum.inl x : Sum α β)) Bool.false := Omega.rfl

theorem isRight_inr {α : Type u} {β : Type v} {x : β} :
    Eq (Sum.isRight (Sum.inr x : Sum α β)) Bool.true := Omega.rfl

theorem map_inl {α : Type u} {α' : Type v} {β : Type w} {β' : Type z} (f : α → α') (g : β → β') (x : α) :
    Eq (Sum.map f g (Sum.inl x)) (Sum.inl (f x)) := Omega.rfl

theorem map_inr {α : Type u} {α' : Type v} {β : Type w} {β' : Type z} (f : α → α') (g : β → β') (x : β) :
    Eq (Sum.map f g (Sum.inr x)) (Sum.inr (g x)) := Omega.rfl

theorem swap_inl {α : Type u} {β : Type v} {x : α} :
    Eq (Sum.swap (Sum.inl x : Sum α β)) (Sum.inr x) := Omega.rfl

theorem swap_inr {α : Type u} {β : Type v} {x : β} :
    Eq (Sum.swap (Sum.inr x : Sum α β)) (Sum.inl x) := Omega.rfl

end Omega.Sum

end
end

namespace Omega.Sum

@[expose, implicit_reducible] public def getLeft {α : Type u} {β : Type v} :
    (ab : Sum α β) → Eq ab.isLeft Bool.true → α :=
  fun ab => Sum.casesOn (motive := fun x => Eq x.isLeft Bool.true → α) ab
    (fun a _ => a) (fun _ h => False.elim (Bool.decEq._proof_1 Bool.false Bool.true h))

@[expose, implicit_reducible] public def getRight {α : Type u} {β : Type v} :
    (ab : Sum α β) → Eq ab.isRight Bool.true → β :=
  fun ab => Sum.casesOn (motive := fun x => Eq x.isRight Bool.true → β) ab
    (fun _ h => False.elim (Bool.decEq._proof_1 Bool.false Bool.true h)) (fun b _ => b)

end Omega.Sum

port_proof Sum.getLeft_inl by_reflexivity
port_proof Sum.getRight_inr by_reflexivity
port_proof Sum.getLeft.congr_simp
port_proof Sum.getRight.congr_simp

port_inductive Sum.LiftRel
port_inductive Sum.Lex
port_proof Sum.liftRel_inl_inl
port_proof Sum.liftRel_inr_inr
port_proof Sum.not_liftRel_inl_inr
port_proof Sum.not_liftRel_inr_inl
port_proof Sum.lex_inl_inl
port_proof Sum.lex_inr_inr
port_proof Sum.lex_inr_inl
port_definition Sum.instDecidableLiftRel.match_1
port_definition Sum.instDecidableLiftRel with_native_code
port_definition Sum.instDecidableRelSumLex.match_1
port_definition Sum.instDecidableRelSumLex with_native_code
attribute [instance] Omega.Sum.instDecidableLiftRel Omega.Sum.instDecidableRelSumLex
