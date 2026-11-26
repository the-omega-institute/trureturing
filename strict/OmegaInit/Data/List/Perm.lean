/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.List.Lemmas

port_proof List.isEmpty.eq_1 by_reflexivity
port_proof List.isEmpty.eq_2 by_reflexivity

@[expose] public section

namespace Omega.List

protected theorem Perm.refl {α : Type u} (l : List α) : Perm l l :=
  List.rec (motive := fun xs => Perm xs xs) .nil (fun a _ ih => Perm.cons a ih) l

end Omega.List

port_proof List.Perm.rfl
port_proof List.Perm.of_eq
port_proof List.Perm.symm
port_proof List.perm_comm
port_proof List.Perm.congr_left
port_proof List.Perm.congr_right
port_proof List.Perm.swap'
port_proof List.Perm.recOnSwap'

namespace Omega.List

theorem Perm.length_eq {α : Type u} {l₁ l₂ : List α} (p : Perm l₁ l₂) : Eq (length l₁) (length l₂) :=
  Perm.rec (motive := fun xs ys _ => Eq (length xs) (length ys)) Omega.rfl
    (fun _ {_ _} _ ih => congrArg Nat.succ ih) (fun _ _ _ => Omega.rfl)
    (fun {_ _ _} _ _ h₁ h₂ => h₁.trans h₂) p

theorem Perm.append_right {α : Type u} {l₁ l₂ : List α} (t₁ : List α) (p : Perm l₁ l₂) :
    Perm (List.append l₁ t₁) (List.append l₂ t₁) :=
  Perm.rec (motive := fun xs ys _ => Perm (List.append xs t₁) (List.append ys t₁)) (Perm.refl t₁)
    (fun x {_ _} _ ih => Perm.cons x ih) (fun x y l => Perm.swap x y (List.append l t₁))
    (fun {_ _ _} _ _ h₁ h₂ => h₁.trans h₂) p

theorem Perm.append_left {α : Type u} {t₁ t₂ : List α} (l : List α) :
    Perm t₁ t₂ → Perm (List.append l t₁) (List.append l t₂) := fun h =>
  List.rec (motive := fun xs => Perm (List.append xs t₁) (List.append xs t₂)) h
    (fun a _ ih => Perm.cons a ih) l

theorem Perm.append {α : Type u} {l₁ l₂ t₁ t₂ : List α} (p₁ : Perm l₁ l₂) (p₂ : Perm t₁ t₂) :
    Perm (List.append l₁ t₁) (List.append l₂ t₂) :=
  (p₁.append_right t₁).trans (p₂.append_left l₂)

theorem Perm.append_cons {α : Type u} (a : α) {l₁ l₂ r₁ r₂ : List α} (p₁ : Perm l₁ l₂) (p₂ : Perm r₁ r₂) :
    Perm (List.append l₁ (List.cons a r₁)) (List.append l₂ (List.cons a r₂)) := p₁.append (p₂.cons a)

theorem perm_middle {α : Type u} {a : α} {l₁ l₂ : List α} :
    Perm (List.append l₁ (cons a l₂)) (cons a (List.append l₁ l₂)) :=
  List.rec (motive := fun xs => Perm (List.append xs (cons a l₂)) (cons a (List.append xs l₂)))
    Perm.rfl (fun b xs ih => (Perm.cons b ih).trans (Perm.swap a b (List.append xs l₂))) l₁

theorem perm_append_singleton {α : Type u} (a : α) (l : List α) : Perm (List.append l (cons a nil)) (cons a l) :=
  perm_middle.trans (Perm.of_eq (congrArg (cons a) (append_nil l)))

theorem perm_append_comm {α : Type u} {l₁ l₂ : List α} : Perm (List.append l₁ l₂) (List.append l₂ l₁) :=
  List.rec (motive := fun xs => Perm (List.append xs l₂) (List.append l₂ xs))
    (Perm.of_eq (append_nil l₂).symm) (fun x _ ih => (Perm.cons x ih).trans perm_middle.symm) l₁

theorem perm_append_comm_assoc {α : Type u} (l₁ l₂ l₃ : List α) :
    Perm (List.append l₁ (List.append l₂ l₃)) (List.append l₂ (List.append l₁ l₃)) :=
  (Perm.of_eq (append_assoc l₁ l₂ l₃).symm).trans
    ((perm_append_comm.append_right l₃).trans (Perm.of_eq (append_assoc l₂ l₁ l₃)))

theorem concat_perm {α : Type u} (l : List α) (a : α) : Perm (concat l a) (cons a l) :=
  (Perm.of_eq concat_eq_append).trans (perm_append_singleton a l)

theorem reverse_perm {α : Type u} (l : List α) : Perm (reverse l) l :=
  List.rec (motive := fun xs => Perm (reverse xs) xs) .nil (fun a xs ih =>
    (Perm.of_eq reverse_cons).trans ((perm_append_singleton a (reverse xs)).trans (Perm.cons a ih))) l

theorem Perm.map {α : Type u} {β : Type v} (f : α → β) {l₁ l₂ : List α} (p : Perm l₁ l₂) :
    Perm (List.map f l₁) (List.map f l₂) :=
  Perm.rec (motive := fun xs ys _ => Perm (List.map f xs) (List.map f ys)) .nil
    (fun x {_ _} _ ih => Perm.cons (f x) ih) (fun x y xs => Perm.swap (f x) (f y) (List.map f xs))
    (fun {_ _ _} _ _ h₁ h₂ => h₁.trans h₂) p

theorem Perm.eq_nil {α : Type u} {l : List α} (p : Perm l List.nil) : Eq l List.nil := eq_nil_of_length_eq_zero p.length_eq

theorem Perm.nil_eq {α : Type u} {l : List α} (p : Perm List.nil l) : Eq List.nil l := p.symm.eq_nil.symm

theorem perm_nil {α : Type u} {l₁ : List α} : Iff (Perm l₁ nil) (Eq l₁ nil) := Iff.intro Perm.eq_nil Perm.of_eq

theorem nil_perm {α : Type u} {l₁ : List α} : Iff (Perm nil l₁) (Eq l₁ nil) :=
  Iff.intro (fun h => h.symm.eq_nil) (fun e => (Perm.of_eq e).symm)

theorem not_perm_nil_cons {α : Type u} (x : α) (l : List α) : Not (Perm nil (cons x l)) :=
  fun h => cons_ne_nil x l h.symm.eq_nil

theorem not_perm_cons_nil {α : Type u} {l : List α} {a : α} : Not (Perm (cons a l) nil) :=
  fun h => cons_ne_nil a l h.eq_nil

end Omega.List
