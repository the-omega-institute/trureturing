/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega.List

protected def singleton {α : Type u} (a : α) : List α := cons a nil

def isEmpty {α : Type u} : List α → Bool :=
  fun xs => List.casesOn (motive := fun _ => Bool) xs Bool.true (fun _ _ => Bool.false)

def head? {α : Type u} : List α → Option α :=
  fun xs => List.casesOn (motive := fun _ => Option α) xs Option.none (fun x _ => Option.some x)

def headD {α : Type u} (as : List α) (fallback : α) : α :=
  List.casesOn (motive := fun _ => α) as fallback (fun x _ => x)

def tail {α : Type u} : List α → List α :=
  fun xs => List.casesOn (motive := fun _ => List α) xs nil (fun _ rest => rest)

def tail? {α : Type u} : List α → Option (List α) :=
  fun xs => List.casesOn (motive := fun _ => Option (List α)) xs Option.none
    (fun _ rest => Option.some rest)

def tailD {α : Type u} (l fallback : List α) : List α :=
  List.casesOn (motive := fun _ => List α) l fallback (fun _ rest => rest)

def modifyHead {α : Type u} (f : α → α) : List α → List α :=
  fun xs => List.casesOn (motive := fun _ => List α) xs nil (fun x rest => cons (f x) rest)

theorem head?_cons {α : Type u} {a : α} {l : List α} :
    Eq (List.head? (List.cons a l)) (Option.some a) := Omega.rfl

theorem head?_nil {α : Type u} :
    Eq (List.head? (List.nil : List α)) Option.none := Omega.rfl

theorem headD_cons {α : Type u} {a : α} {l : List α} {d : α} :
    Eq (List.headD (List.cons a l) d) a := Omega.rfl

theorem headD_nil {α : Type u} {d : α} :
    Eq (List.headD (List.nil : List α) d) d := Omega.rfl

theorem isEmpty_cons {α : Type u} {x : α} {xs : List α} :
    Eq (List.isEmpty (List.cons x xs)) Bool.false := Omega.rfl

theorem isEmpty_nil {α : Type u} :
    Eq (List.isEmpty (List.nil : List α)) Bool.true := Omega.rfl

theorem modifyHead_cons {α : Type u} {a : α} {l : List α} {f : α → α} :
    Eq (List.modifyHead f (List.cons a l)) (List.cons (f a) l) := Omega.rfl

theorem modifyHead_nil {α : Type u} {f : α → α} :
    Eq (List.modifyHead f (List.nil : List α)) List.nil := Omega.rfl

theorem tail?_cons {α : Type u} {a : α} {l : List α} :
    Eq (List.tail? (List.cons a l)) (Option.some l) := Omega.rfl

theorem tail?_nil {α : Type u} :
    Eq (List.tail? (List.nil : List α)) Option.none := Omega.rfl

theorem tailD_cons {α : Type u} {a : α} {l l' : List α} :
    Eq (List.tailD (List.cons a l) l') l := Omega.rfl

theorem tailD_nil {α : Type u} {l' : List α} :
    Eq (List.tailD (List.nil : List α) l') l' := Omega.rfl

theorem tail_cons {α : Type u} {a : α} {as : List α} :
    Eq (List.tail (List.cons a as)) as := Omega.rfl

theorem tail_nil {α : Type u} :
    Eq (List.tail (List.nil : List α)) List.nil := Omega.rfl

end Omega.List

port_proof List.modifyHead.eq_1 by_reflexivity
port_proof List.modifyHead.eq_2 by_reflexivity
