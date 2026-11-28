/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Kim Morrison, Jannis Limperg
-/
module
prelude
public import OmegaInit.Data.List.Attach
public import OmegaInit.Data.List.Basic
public import OmegaInit.Data.Option.Basic
import OmegaInit.Data.Bool

namespace Omega.List

private theorem findPos {α : Type u} {p : α → Bool} {a : α} {l : List α}
    (h : Eq (p a) Bool.true) : Eq (find? p (cons a l)) (Option.some a) :=
  (find?_cons (a := a) (as := l) (p := p)).trans
    (congrArg (fun value => filter.match_1 (fun _ => Option α) value
      (fun _ => Option.some a) (fun _ => find? p l)) h)

private theorem findNeg {α : Type u} {p : α → Bool} {a : α} {l : List α}
    (h : Not (Eq (p a) Bool.true)) : Eq (find? p (cons a l)) (find? p l) :=
  (find?_cons (a := a) (as := l) (p := p)).trans
    (congrArg (fun value => filter.match_1 (fun _ => Option α) value
      (fun _ => Option.some a) (fun _ => find? p l)) (Bool.eq_false_of_ne_true h))

private theorem findSomePos {α : Type u} {β : Type v} {f : α → Option β} {a : α} {l : List α}
    (h : Eq (Option.isSome (f a)) Bool.true) : Eq (findSome? f (cons a l)) (f a) :=
  (findSome?_cons (a := a) (as := l) (f := f)).trans
    (Option.casesOn (motive := fun value => Eq value.isSome Bool.true →
      Eq (findSome?.match_1 (fun _ => Option β) value Option.some (fun _ => findSome? f l)) value)
      (f a) (fun impossible => False.elim (Bool.false_ne_true (Option.isSome_none.symm.trans impossible)))
      (fun _ _ => Omega.rfl) h)

private theorem findSomeNeg {α : Type u} {β : Type v} {f : α → Option β} {a : α} {l : List α}
    (h : Eq (Option.isNone (f a)) Bool.true) : Eq (findSome? f (cons a l)) (findSome? f l) :=
  (findSome?_cons (a := a) (as := l) (f := f)).trans
    (Option.casesOn (motive := fun value => Eq value.isNone Bool.true →
      Eq (findSome?.match_1 (fun _ => Option β) value Option.some (fun _ => findSome? f l)) (findSome? f l))
      (f a) (fun _ => Omega.rfl)
      (fun _ impossible => False.elim (Bool.false_ne_true (Option.isNone_some.symm.trans impossible))) h)

end Omega.List

port_proof List.find?_cons_of_pos using Omega.List.findPos
port_proof List.find?_cons_of_neg using Omega.List.findNeg
port_proof List.findSome?_cons_of_isSome using Omega.List.findSomePos
port_proof List.findSome?_cons_of_isNone using Omega.List.findSomeNeg
port_proof List.idxOf?_nil by_reflexivity
port_proof List.finIdxOf?_nil by_reflexivity
port_proof List.findIdx?_nil by_reflexivity
port_proof List.findFinIdx?_nil by_reflexivity
