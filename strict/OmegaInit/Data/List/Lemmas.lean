/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Kim Morrison
-/
module
prelude
public import OmegaInit.Core
public import OmegaInit.Data.List.Basic
import OmegaInit.Data.Nat.Basic

port_proof List.exists_cons_of_ne_nil
port_proof List.head?_singleton by_reflexivity
port_proof List.tailD_eq_tail?
port_proof List.tail_eq_tailD by_reflexivity
port_proof absurd.congr_simp by_reflexivity
port_proof List.headD.eq_1 by_reflexivity
port_proof List.headD.eq_2 by_reflexivity

@[expose] public section

namespace Omega.List

theorem reverse_singleton {α : Type u} {a : α} :
    Eq (reverse (cons a nil)) (cons a nil) := Omega.rfl

theorem reverse_append {α : Type u} {as bs : List α} :
    Eq (reverse (List.append as bs)) (List.append (reverse bs) (reverse as)) :=
  List.rec (motive := fun xs => Eq (reverse (List.append xs bs)) (List.append (reverse bs) (reverse xs)))
    (append_nil (reverse bs)).symm
    (fun a xs ih => (reverse_cons (a := a) (as := List.append xs bs)).trans
      ((congrArg (fun zs => List.append zs (cons a nil)) ih).trans
        ((append_assoc (reverse bs) (reverse xs) (cons a nil)).trans
          (congrArg (List.append (reverse bs)) (reverse_cons (a := a) (as := xs)).symm)))) as

theorem reverse_concat {α : Type u} {l : List α} {a : α} :
    Eq (reverse (List.append l (cons a nil))) (cons a (reverse l)) := reverse_append

theorem reverse_reverse {α : Type u} (as : List α) : Eq (reverse (reverse as)) as :=
  List.rec (motive := fun xs => Eq (reverse (reverse xs)) xs) Omega.rfl
    (fun a xs ih => (congrArg reverse (reverse_cons (a := a) (as := xs))).trans
      (reverse_concat.trans (congrArg (cons a) ih))) as

theorem reverse_eq_iff {α : Type u} {as bs : List α} :
    Iff (Eq (reverse as) bs) (Eq as (reverse bs)) :=
  Iff.intro (fun h => (reverse_reverse as).symm.trans (congrArg reverse h))
    (fun h => (congrArg reverse h).trans (reverse_reverse bs))

theorem reverse_inj {α : Type u} {xs ys : List α} :
    Iff (Eq (reverse xs) (reverse ys)) (Eq xs ys) :=
  Iff.intro (fun h => (reverse_eq_iff.mp h).trans (reverse_reverse ys)) (congrArg reverse)

theorem reverse_eq_nil_iff {α : Type u} {xs : List α} :
    Iff (Eq (reverse xs) nil) (Eq xs nil) := reverse_eq_iff

theorem reverse_ne_nil_iff {α : Type u} {xs : List α} :
    Iff (Ne (reverse xs) nil) (Ne xs nil) :=
  Iff.intro (fun h e => h (reverse_eq_nil_iff.mpr e)) (fun h e => h (reverse_eq_nil_iff.mp e))

theorem reverse_eq_cons_iff {α : Type u} {xs : List α} {a : α} {ys : List α} :
    Iff (Eq (reverse xs) (cons a ys)) (Eq xs (List.append (reverse ys) (cons a nil))) :=
  Iff.intro (fun h => (reverse_eq_iff.mp h).trans reverse_cons)
    (fun h => reverse_eq_iff.mpr (h.trans reverse_cons.symm))

theorem reverse_eq_append_iff {α : Type u} {xs ys zs : List α} :
    Iff (Eq (reverse xs) (List.append ys zs)) (Eq xs (List.append (reverse zs) (reverse ys))) :=
  Iff.intro (fun h => (reverse_eq_iff.mp h).trans reverse_append)
    (fun h => reverse_eq_iff.mpr (h.trans reverse_append.symm))

theorem length_reverse {α : Type u} {as : List α} : Eq (length (reverse as)) (length as) :=
  List.rec (motive := fun xs => Eq (length (reverse xs)) (length xs)) Omega.rfl
    (fun a xs ih => (congrArg length (reverse_cons (a := a) (as := xs))).trans
      (length_append.trans ((Nat.add_one (length (reverse xs))).trans (congrArg Nat.succ ih)))) as

theorem length_map {α : Type u} {β : Type v} {as : List α} (f : α → β) : Eq (length (map f as)) (length as) :=
  List.rec (motive := fun xs => Eq (length (map f xs)) (length xs)) Omega.rfl
    (fun _ _ ih => congrArg Nat.succ ih) as

theorem isEmpty_map {α : Type u} {β : Type v} {l : List α} {f : α → β} : Eq (isEmpty (map f l)) (isEmpty l) :=
  List.casesOn (motive := fun xs => Eq (isEmpty (map f xs)) (isEmpty xs))
    l Omega.rfl (fun _ _ => Omega.rfl)

theorem map_id'' {α : Type u} {f : α → α} (h : ∀ x, Eq (f x) x) (l : List α) : Eq (map f l) l :=
  List.rec (motive := fun xs => Eq (map f xs) xs) Omega.rfl
    (fun x xs ih => (congrArg (cons (f x)) ih).trans (congrArg (fun a => cons a xs) (h x))) l

theorem map_id {α : Type u} (l : List α) : Eq (map id l) l := map_id'' (fun _ => Omega.rfl) l

theorem map_append {α : Type u} {β : Type v} {f : α → β} {l₁ l₂ : List α} :
    Eq (map f (List.append l₁ l₂)) (List.append (map f l₁) (map f l₂)) :=
  List.rec (motive := fun xs => Eq (map f (List.append xs l₂)) (List.append (map f xs) (map f l₂)))
    Omega.rfl (fun a _ ih => congrArg (cons (f a)) ih) l₁

theorem map_map {β : Type u} {γ : Type v} {α : Type w} {g : β → γ} {f : α → β} {l : List α} :
    Eq (map g (map f l)) (map (fun a => g (f a)) l) :=
  List.rec (motive := fun xs => Eq (map g (map f xs)) (map (fun a => g (f a)) xs)) Omega.rfl
    (fun a _ ih => congrArg (cons (g (f a))) ih) l

theorem map_concat {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List α} :
    Eq (map f (concat l a)) (concat (map f l) (f a)) :=
  List.rec (motive := fun xs => Eq (map f (concat xs a)) (concat (map f xs) (f a)))
    Omega.rfl (fun x _ ih => congrArg (cons (f x)) ih) l

theorem map_reverse {α : Type u} {β : Type v} {f : α → β} {l : List α} :
    Eq (map f (reverse l)) (reverse (map f l)) :=
  List.rec (motive := fun xs => Eq (map f (reverse xs)) (reverse (map f xs))) Omega.rfl
    (fun a xs ih => (congrArg (map f) (reverse_cons (a := a) (as := xs))).trans
      (map_append.trans ((congrArg (fun ys => List.append ys (cons (f a) nil)) ih).trans reverse_cons.symm))) l

theorem flatten_append {α : Type u} {L₁ L₂ : List (List α)} :
    Eq (flatten (List.append L₁ L₂)) (List.append (flatten L₁) (flatten L₂)) :=
  List.rec (motive := fun xs => Eq (flatten (List.append xs L₂)) (List.append (flatten xs) (flatten L₂)))
    Omega.rfl (fun l ls ih => (congrArg (List.append l) ih).trans (append_assoc l (flatten ls) (flatten L₂)).symm) L₁

theorem map_flatten {α : Type u} {β : Type v} {f : α → β} {L : List (List α)} :
    Eq (map f (flatten L)) (flatten (map (map f) L)) :=
  List.rec (motive := fun ls => Eq (map f (flatten ls)) (flatten (map (map f) ls)))
    Omega.rfl (fun xs _ ih => map_append.trans (congrArg (List.append (map f xs)) ih)) L

theorem flatMap_id {α : Type u} {L : List (List α)} : Eq (flatMap id L) (flatten L) :=
  congrArg flatten (map_id L)

theorem flatMap_assoc {α : Type u} {β : Type v} {γ : Type w} {l : List α} {f : α → List β} {g : β → List γ} :
    Eq (flatMap g (flatMap f l)) (flatMap (fun x => flatMap g (f x)) l) :=
  List.rec (motive := fun xs => Eq (flatMap g (flatMap f xs)) (flatMap (fun x => flatMap g (f x)) xs))
    Omega.rfl (fun a _ ih => flatMap_append.trans (congrArg (List.append (flatMap g (f a))) ih)) l

theorem map_flatMap {β : Type u} {γ : Type v} {α : Type w} {f : β → γ} {g : α → List β} {l : List α} :
    Eq (map f (flatMap g l)) (flatMap (fun a => map f (g a)) l) :=
  List.rec (motive := fun xs => Eq (map f (flatMap g xs)) (flatMap (fun a => map f (g a)) xs))
    Omega.rfl (fun a _ ih => map_append.trans (congrArg (List.append (map f (g a))) ih)) l

theorem flatMap_map {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → List γ) (l : List α) :
    Eq (flatMap g (map f l)) (flatMap (fun a => g (f a)) l) := congrArg flatten map_map

theorem foldl_append {α : Type u} {β : Type v} {f : β → α → β} {b : β} {l l' : List α} :
    Eq (foldl f b (List.append l l')) (foldl f (foldl f b l) l') :=
  List.rec (motive := fun xs => ∀ acc, Eq (foldl f acc (List.append xs l')) (foldl f (foldl f acc xs) l'))
    (fun _ => Omega.rfl) (fun a _ ih acc => ih (f acc a)) l b

theorem foldr_append {α : Type u} {β : Type v} {f : α → β → β} {b : β} {l l' : List α} :
    Eq (foldr f b (List.append l l')) (foldr f (foldr f b l') l) :=
  List.rec (motive := fun xs => Eq (foldr f b (List.append xs l')) (foldr f (foldr f b l') xs))
    Omega.rfl (fun a _ ih => congrArg (f a) ih) l

theorem cons_ne_nil {α : Type u} (a : α) (l : List α) : Ne (cons a l) nil :=
  fun h => Bool.ne_true_of_eq_false Omega.rfl (congrArg isEmpty h)

theorem cons_inj_right {α : Type u} (a : α) {l l' : List α} :
    Iff (Eq (cons a l) (cons a l')) (Eq l l') :=
  Iff.intro (congrArg tail) (congrArg (cons a))

theorem cons_eq_cons {α : Type u} {a b : α} {l l' : List α} :
    Iff (Eq (cons a l) (cons b l')) (And (Eq a b) (Eq l l')) :=
  Iff.intro (fun h => And.intro (congrArg (fun xs => headD xs a) h) (congrArg tail h))
    (fun h => (congrArg (fun x => cons x l) h.left).trans (congrArg (cons b) h.right))

theorem singleton_inj {α : Type u} {a b : α} : Iff (Eq (cons a nil) (cons b nil)) (Eq a b) :=
  Iff.intro (fun h => (cons_eq_cons.mp h).left) (congrArg (fun x => cons x nil))

theorem append_right_inj {α : Type u} {t₁ t₂ : List α} (s : List α) :
    Iff (Eq (List.append s t₁) (List.append s t₂)) (Eq t₁ t₂) :=
  List.rec (motive := fun xs => Iff (Eq (List.append xs t₁) (List.append xs t₂)) (Eq t₁ t₂))
    Iff.rfl (fun a _ ih => Iff.intro (fun h => ih.mp ((cons_inj_right a).mp h))
      (fun h => congrArg (cons a) (ih.mpr h))) s

theorem append_left_inj {α : Type u} {s₁ s₂ : List α} (t : List α) :
    Iff (Eq (List.append s₁ t) (List.append s₂ t)) (Eq s₁ s₂) :=
  Iff.intro (fun h => reverse_inj.mp ((append_right_inj (reverse t)).mp
    (reverse_append.symm.trans ((congrArg reverse h).trans reverse_append))))
    (congrArg (fun xs => List.append xs t))

end Omega.List

port_proof List.map_id' using Omega.List.map_id
port_proof List.map_singleton by_reflexivity
port_proof List.flatMap_id' using Omega.List.flatMap_id
port_proof List.flatMap_def by_reflexivity
port_proof List.concat_nil by_reflexivity
port_proof List.concat_cons by_reflexivity

namespace Omega.List

theorem append_eq_nil_iff : Iff (Eq (List.append p q) nil) (And (Eq p nil) (Eq q nil)) :=
  List.casesOn (motive := fun xs => Iff (Eq (List.append xs q) nil) (And (Eq xs nil) (Eq q nil)))
    p (Iff.intro (fun h => And.intro Omega.rfl h) (fun h => h.right))
    (fun a xs => Iff.intro (fun h => False.elim (cons_ne_nil a (List.append xs q) h))
      (fun h => False.elim (cons_ne_nil a xs h.left)))

theorem nil_eq_append_iff : Iff (Eq nil (List.append a b)) (And (Eq a nil) (Eq b nil)) :=
  Iff.intro (fun h => append_eq_nil_iff.mp h.symm) (fun h => (append_eq_nil_iff.mpr h).symm)

theorem eq_nil_of_append_eq_nil {α : Type u} {l₁ l₂ : List α} (h : Eq (List.append l₁ l₂) nil) :
    And (Eq l₁ nil) (Eq l₂ nil) := append_eq_nil_iff.mp h

theorem append_ne_nil_of_left_ne_nil {α : Type u} {s : List α} (h : Ne s nil) (t : List α) :
    Ne (List.append s t) nil := fun e => h (append_eq_nil_iff.mp e).left

theorem append_ne_nil_of_right_ne_nil {α : Type u} {t : List α} (s : List α) :
    Ne t nil → Ne (List.append s t) nil := fun h e => h (append_eq_nil_iff.mp e).right

theorem concat_ne_nil {α : Type u} (a : α) (l : List α) : Ne (List.append l (cons a nil)) nil :=
  append_ne_nil_of_right_ne_nil l (cons_ne_nil a nil)

theorem append_right_eq_self {α : Type u} {xs ys : List α} :
    Iff (Eq (List.append xs ys) xs) (Eq ys nil) :=
  Iff.intro (fun h => (append_right_inj xs).mp (h.trans (append_nil xs).symm))
    (fun h => (congrArg (List.append xs) h).trans (append_nil xs))

theorem self_eq_append_right {α : Type u} {xs ys : List α} :
    Iff (Eq xs (List.append xs ys)) (Eq ys nil) :=
  Iff.intro (fun h => append_right_eq_self.mp h.symm) (fun h => (append_right_eq_self.mpr h).symm)

theorem append_left_eq_self {α : Type u} {xs ys : List α} :
    Iff (Eq (List.append xs ys) ys) (Eq xs nil) :=
  Iff.intro (fun h => (append_left_inj ys).mp (h.trans (nil_append ys).symm))
    (fun h => (congrArg (fun l => List.append l ys) h).trans (nil_append ys))

theorem self_eq_append_left {α : Type u} {xs ys : List α} :
    Iff (Eq ys (List.append xs ys)) (Eq xs nil) :=
  Iff.intro (fun h => append_left_eq_self.mp h.symm) (fun h => (append_left_eq_self.mpr h).symm)

theorem eq_nil_of_length_eq_zero : Eq (length l) Nat.zero → Eq l nil :=
  List.casesOn (motive := fun xs => Eq (length xs) Nat.zero → Eq xs nil) l
    (fun _ => Omega.rfl) (fun _ xs h => False.elim (Nat.succ_ne_zero (length xs) h))

theorem length_eq_zero_iff : Iff (Eq (length l) Nat.zero) (Eq l nil) :=
  Iff.intro eq_nil_of_length_eq_zero (congrArg length)

theorem isEmpty_iff {α : Type u} {l : List α} : Iff (Eq (isEmpty l) Bool.true) (Eq l nil) :=
  List.casesOn (motive := fun xs => Iff (Eq (isEmpty xs) Bool.true) (Eq xs nil)) l
    (Iff.intro (fun _ => Omega.rfl) (fun _ => Omega.rfl))
    (fun a xs => Iff.intro (fun h => False.elim (Bool.ne_true_of_eq_false Omega.rfl h))
      (fun h => False.elim (cons_ne_nil a xs h)))

theorem isEmpty_eq_false_iff {α : Type u} {l : List α} : Iff (Eq (isEmpty l) Bool.false) (Ne l nil) :=
  Iff.intro (fun h e => Bool.ne_true_of_eq_false h (isEmpty_iff.mpr e))
    (fun h => Bool.eq_false_of_ne_true (fun e => h (isEmpty_iff.mp e)))

theorem isEmpty_iff_length_eq_zero {α : Type u} {l : List α} :
    Iff (Eq (isEmpty l) Bool.true) (Eq (length l) Nat.zero) :=
  Iff.intro (fun h => length_eq_zero_iff.mpr (isEmpty_iff.mp h))
    (fun h => isEmpty_iff.mpr (length_eq_zero_iff.mp h))

theorem reverseAux_reverseAux_nil {α : Type u} {as bs : List α} :
    Eq (reverseAux (reverseAux as bs) nil) (reverseAux bs as) :=
  reverseAux_reverseAux.trans (congrArg (reverseAux bs) (reverse_reverse as))

theorem head_eq_of_cons_eq (H : Eq (cons h₁ t₁) (cons h₂ t₂)) : Eq h₁ h₂ := (cons_eq_cons.mp H).left

theorem tail_eq_of_cons_eq (H : Eq (cons h₁ t₁) (cons h₂ t₂)) : Eq t₁ t₂ := (cons_eq_cons.mp H).right

theorem filter_cons_of_pos {α : Type u} {p : α → Bool} {a : α} {l : List α} (pa : Eq (p a) Bool.true) :
    Eq (filter p (cons a l)) (cons a (filter p l)) :=
  congrArg (fun bit => Bool.rec (motive := fun _ => List α) (filter p l) (cons a (filter p l)) bit) pa

theorem filter_cons_of_neg {α : Type u} {p : α → Bool} {a : α} {l : List α} (pa : Not (Eq (p a) Bool.true)) :
    Eq (filter p (cons a l)) (filter p l) :=
  congrArg (fun bit => Bool.rec (motive := fun _ => List α) (filter p l) (cons a (filter p l)) bit)
    (Bool.eq_false_of_ne_true pa)

/- Open: List.filterMap_eq_filter asks for equality of the two functions before a
list is supplied. The pinned public bodies of filterMap and filter recurse with
different steps. The pointwise agreement follows by list induction and a Boolean
case split, as in OmegaChecks.InitPort.Alternatives.List.filterGuard. -/
theorem filterMap_cons_some {α : Type u} {β : Type v} {f : α → Option β} {a : α} {l : List α} {b : β}
    (h : Eq (f a) (Option.some b)) : Eq (filterMap f (cons a l)) (cons b (filterMap f l)) :=
  congrArg (fun o => Option.casesOn (motive := fun _ => List β) o (filterMap f l) (fun x => cons x (filterMap f l))) h

theorem filterMap_cons_none {α : Type u} {β : Type v} {f : α → Option β} {a : α} {l : List α}
    (h : Eq (f a) Option.none) : Eq (filterMap f (cons a l)) (filterMap f l) :=
  congrArg (fun o => Option.casesOn (motive := fun _ => List β) o (filterMap f l) (fun x => cons x (filterMap f l))) h

theorem filterMap_some {α : Type u} {l : List α} : Eq (filterMap Option.some l) l :=
  List.rec (motive := fun xs => Eq (filterMap Option.some xs) xs) Omega.rfl (fun a _ ih => congrArg (cons a) ih) l

end Omega.List

namespace Omega.List

theorem not_mem_nil {α : Type u} {a : α} : Not (Mem a nil) :=
  fun h => Mem.rec (motive := fun xs _ => List.casesOn (motive := fun _ => Prop) xs False (fun _ _ => True))
    (fun _ => True.intro) (fun _ {_} _ _ => True.intro) h

theorem mem_cons : Iff ((fun xs x => Mem x xs) (cons b l) a) (Or (Eq a b) (Mem a l)) :=
  Iff.intro (fun h => Mem.rec (motive := fun xs _ =>
    List.casesOn (motive := fun _ => Prop) xs False (fun b ys => Or (Eq a b) (Mem a ys)))
    (fun _ => Or.inl Omega.rfl) (fun _ {_} prev _ => Or.inr prev) h)
    (fun h => h.elim (fun e => Eq.subst (motive := fun x => Mem a (cons x l)) e (Mem.head l))
      (Mem.tail b))

theorem eq_or_mem_of_mem_cons {α : Type u} {a b : α} {l : List α} :
    Mem a (cons b l) → Or (Eq a b) (Mem a l) := mem_cons.mp

theorem mem_cons_self {α : Type u} {a : α} {l : List α} : Mem a (cons a l) := Mem.head l

theorem mem_cons_of_mem {α : Type u} (y : α) {a : α} {l : List α} : Mem a l → Mem a (cons y l) := Mem.tail y

set_option relaxedAutoImplicit true in
theorem mem_append_cons_self : (fun xs x => Mem x xs) (List.append xs (cons a ys)) a := mem_append_right xs mem_cons_self

theorem mem_concat_self {α : Type u} {xs : List α} {a : α} : Mem a (List.append xs (cons a nil)) :=
  mem_append_right xs mem_cons_self

theorem mem_append {α : Type u} {a : α} {s t : List α} : Iff (Mem a (List.append s t)) (Or (Mem a s) (Mem a t)) :=
  Iff.intro (List.rec (motive := fun xs => Mem a (List.append xs t) → Or (Mem a xs) (Mem a t))
    (fun h => Or.inr h) (fun b _ ih h => (mem_cons.mp h).elim
      (fun e => Or.inl (mem_cons.mpr (Or.inl e)))
      (fun tailMem => (ih tailMem).elim (fun hm => Or.inl (Mem.tail b hm)) Or.inr)) s)
    (fun h => h.elim (mem_append_left t) (mem_append_right s))

theorem mem_singleton {α : Type u} {a b : α} : Iff (Mem a (cons b nil)) (Eq a b) :=
  Iff.intro (fun h => (mem_cons.mp h).elim id (fun hm => False.elim (not_mem_nil hm)))
    (fun e => mem_cons.mpr (Or.inl e))

theorem mem_reverse {α : Type u} {x : α} {as : List α} : Iff (Mem x (reverse as)) (Mem x as) :=
  List.rec (motive := fun xs => Iff (Mem x (reverse xs)) (Mem x xs)) Iff.rfl
    (fun a xs ih =>
      have transport := reverse_cons (a := a) (as := xs)
      Iff.intro (fun h => (mem_append.mp (Eq.subst (motive := Mem x) transport h)).elim
        (fun hm => Mem.tail a (ih.mp hm)) (fun hm => mem_cons.mpr (Or.inl (mem_singleton.mp hm))))
        (fun h => Eq.subst (motive := Mem x) transport.symm (mem_append.mpr
          ((mem_cons.mp h).elim (fun e => Or.inr (mem_singleton.mpr e)) (fun hm => Or.inl (ih.mpr hm)))))) as

end Omega.List

namespace Omega.List

theorem mem_map {α : Type u} {β : Type v} {b : β} {f : α → β} {l : List α} :
    Iff (Mem b (map f l)) (Exists (fun a => And (Mem a l) (Eq (f a) b))) :=
  List.rec (motive := fun xs => Iff (Mem b (map f xs)) (Exists (fun a => And (Mem a xs) (Eq (f a) b))))
    (Iff.intro (fun h => False.elim (not_mem_nil h))
      (fun h => h.elim (fun _ hm => False.elim (not_mem_nil hm.left))))
    (fun x xs ih => Iff.intro
      (fun h => (mem_cons.mp h).elim
        (fun e => Exists.intro x (And.intro (Mem.head xs) e.symm))
        (fun hm => (ih.mp hm).elim (fun a ha => Exists.intro a (And.intro (Mem.tail x ha.left) ha.right))))
      (fun h => h.elim (fun a ha => (mem_cons.mp ha.left).elim
        (fun e => mem_cons.mpr (Or.inl (ha.right.symm.trans (congrArg f e))))
        (fun hm => Mem.tail (f x) (ih.mpr (Exists.intro a (And.intro hm ha.right))))))) l

theorem mem_map_of_mem {α : Type u} {β : Type v} {l : List α} {a : α} {f : α → β} (h : Mem a l) :
    Mem (f a) (map f l) := mem_map.mpr (Exists.intro a (And.intro h Omega.rfl))

theorem mem_flatten {α : Type u} {a : α} {L : List (List α)} :
    Iff (Mem a (flatten L)) (Exists (fun l => And (Mem l L) (Mem a l))) :=
  List.rec (motive := fun xs => Iff (Mem a (flatten xs)) (Exists (fun l => And (Mem l xs) (Mem a l))))
    (Iff.intro (fun h => False.elim (not_mem_nil h))
      (fun h => h.elim (fun _ hm => False.elim (not_mem_nil hm.left))))
    (fun xs ls ih => Iff.intro
      (fun h => (mem_append.mp h).elim (fun hm => Exists.intro xs (And.intro (Mem.head ls) hm))
        (fun hm => (ih.mp hm).elim (fun l hl => Exists.intro l (And.intro (Mem.tail xs hl.left) hl.right))))
      (fun h => h.elim (fun l hl => mem_append.mpr ((mem_cons.mp hl.left).elim
        (fun e => Or.inl (Eq.subst (motive := Mem a) e hl.right))
        (fun hm => Or.inr (ih.mpr (Exists.intro l (And.intro hm hl.right)))))))) L

theorem mem_flatMap {α : Type u} {β : Type v} {f : α → List β} {b : β} {l : List α} :
    Iff (Mem b (flatMap f l)) (Exists (fun a => And (Mem a l) (Mem b (f a)))) :=
  Iff.intro (fun h => (mem_flatten.mp h).elim (fun _ hxs =>
    (mem_map.mp hxs.left).elim (fun a ha => Exists.intro a
      (And.intro ha.left (Eq.subst (motive := Mem b) ha.right.symm hxs.right)))))
    (fun h => h.elim (fun a ha => mem_flatten.mpr
      (Exists.intro (f a) (And.intro (mem_map_of_mem ha.left) ha.right))))

theorem mem_flatMap_of_mem {β : Type u} {α : Type v} {b : β} {l : List α} {f : α → List β} {a : α}
    (al : Mem a l) (h : Mem b (f a)) : Mem b (flatMap f l) :=
  mem_flatMap.mpr (Exists.intro a (And.intro al h))

theorem foldr_cons_nil {α : Type u} {l : List α} : Eq (foldr cons nil l) l :=
  List.rec (motive := fun xs => Eq (foldr cons nil xs) xs) Omega.rfl (fun a _ ih => congrArg (cons a) ih) l

theorem foldr_map {α₁ : Type u} {α₂ : Type v} {β : Type w} {f : α₁ → α₂} {g : α₂ → β → β}
    {l : List α₁} {init : β} : Eq (foldr g init (map f l)) (foldr (fun x y => g (f x) y) init l) :=
  List.rec (motive := fun xs => Eq (foldr g init (map f xs)) (foldr (fun x y => g (f x) y) init xs))
    Omega.rfl (fun a _ ih => congrArg (g (f a)) ih) l

theorem foldl_map {β₁ : Type u} {β₂ : Type v} {α : Type w} {f : β₁ → β₂} {g : α → β₂ → α}
    {l : List β₁} {init : α} : Eq (foldl g init (map f l)) (foldl (fun x y => g x (f y)) init l) :=
  List.rec (motive := fun xs => ∀ acc, Eq (foldl g acc (map f xs)) (foldl (fun x y => g x (f y)) acc xs))
    (fun _ => Omega.rfl) (fun a _ ih acc => ih (g acc (f a))) l init

theorem foldr_flatten {α : Type u} {β : Type v} {f : α → β → β} {b : β} {L : List (List α)} :
    Eq (foldr f b (flatten L)) (foldr (fun l acc => foldr f acc l) b L) :=
  List.rec (motive := fun ls => Eq (foldr f b (flatten ls)) (foldr (fun l acc => foldr f acc l) b ls))
    Omega.rfl (fun l _ ih => foldr_append.trans (congrArg (fun acc => foldr f acc l) ih)) L

theorem foldl_flatten {β : Type u} {α : Type v} {f : β → α → β} {b : β} {L : List (List α)} :
    Eq (foldl f b (flatten L)) (foldl (fun acc l => foldl f acc l) b L) :=
  List.rec (motive := fun ls => ∀ acc, Eq (foldl f acc (flatten ls)) (foldl (fun acc l => foldl f acc l) acc ls))
    (fun _ => Omega.rfl) (fun l _ ih acc => foldl_append.trans (ih (foldl f acc l))) L b

theorem foldr_flatMap {α : Type u} {β : Type v} {γ : Type w} {f : α → List β} {g : β → γ → γ}
    {l : List α} {init : γ} : Eq (foldr g init (flatMap f l)) (foldr (fun x acc => foldr g acc (f x)) init l) :=
  foldr_flatten.trans foldr_map

theorem foldl_flatMap {α : Type u} {β : Type v} {γ : Type w} {f : α → List β} {g : γ → β → γ}
    {l : List α} {init : γ} : Eq (foldl g init (flatMap f l)) (foldl (fun acc x => foldl g acc (f x)) init l) :=
  foldl_flatten.trans foldl_map

theorem replicate_succ' : Eq (replicate (Nat.succ n) a) (List.append (replicate n a) (cons a nil)) :=
  Nat.rec (motive := fun i => Eq (replicate (Nat.succ i) a) (List.append (replicate i a) (cons a nil)))
    Omega.rfl (fun _ ih => congrArg (cons a) ih) n

theorem reverse_replicate {α : Type u} {n : Nat} {a : α} : Eq (reverse (replicate n a)) (replicate n a) :=
  Nat.rec (motive := fun i => Eq (reverse (replicate i a)) (replicate i a)) Omega.rfl
    (fun i ih => reverse_cons.trans ((congrArg (fun xs => List.append xs (cons a nil)) ih).trans
      (replicate_succ' (n := i) (a := a)).symm)) n

theorem replicate_append_replicate : Eq (List.append (replicate n a) (replicate m a)) (replicate (Nat.add n m) a) :=
  Nat.rec (motive := fun i => Eq (List.append (replicate i a) (replicate m a)) (replicate (Nat.add i m) a))
    (congrArg (fun k => replicate k a) (Nat.zero_add m).symm)
    (fun i ih => (congrArg (cons a) ih).trans (congrArg (fun k => replicate k a) (Nat.succ_add i m).symm)) n

theorem map_replicate : Eq ((replicate n a).map f) (replicate n (f a)) :=
  Nat.rec (motive := fun i => Eq (map f (replicate i a)) (replicate i (f a))) Omega.rfl
    (fun _ ih => congrArg (cons (f a)) ih) n

end Omega.List

namespace Omega.List

theorem filter_append {α : Type u} {p : α → Bool} (l₁ l₂ : List α) :
    Eq (filter p (List.append l₁ l₂)) (List.append (filter p l₁) (filter p l₂)) :=
  List.rec (motive := fun xs => Eq (filter p (List.append xs l₂)) (List.append (filter p xs) (filter p l₂)))
    Omega.rfl (fun a xs ih =>
      let keep := fun bit xs => Bool.rec (motive := fun _ => List α) xs (cons a xs) bit
      Bool.rec (motive := fun bit => Eq (keep bit (filter p (List.append xs l₂)))
        (List.append (keep bit (filter p xs)) (filter p l₂))) ih (congrArg (cons a) ih) (p a)) l₁

theorem filterMap_append {α : Type u} {β : Type v} {l l' : List α} {f : α → Option β} :
    Eq (filterMap f (List.append l l')) (List.append (filterMap f l) (filterMap f l')) :=
  List.rec (motive := fun xs => Eq (filterMap f (List.append xs l')) (List.append (filterMap f xs) (filterMap f l')))
    Omega.rfl (fun a xs ih =>
      let prepend := fun (o : Option β) ys => Option.casesOn (motive := fun _ => List β) o ys (fun b => cons b ys)
      Option.casesOn (motive := fun o => Eq (prepend o (filterMap f (List.append xs l')))
        (List.append (prepend o (filterMap f xs)) (filterMap f l'))) (f a) ih (fun b => congrArg (cons b) ih)) l

theorem length_filter_le {α : Type u} (p : α → Bool) (l : List α) : Nat.le (length (filter p l)) (length l) :=
  List.rec (motive := fun xs => Nat.le (length (filter p xs)) (length xs)) (Nat.le_refl Nat.zero)
    (fun a xs ih => Bool.rec (motive := fun bit => Nat.le (length (Bool.rec (motive := fun _ => List α)
      (filter p xs) (cons a (filter p xs)) bit)) (Nat.succ (length xs)))
      (Nat.le.step ih) (Nat.succ_le_succ ih) (p a)) l

theorem length_filterMap_le {α : Type u} {β : Type v} (f : α → Option β) (l : List α) :
    Nat.le (length (filterMap f l)) (length l) :=
  List.rec (motive := fun xs => Nat.le (length (filterMap f xs)) (length xs)) (Nat.le_refl Nat.zero)
    (fun a xs ih => Option.casesOn (motive := fun o => Nat.le (length (Option.casesOn (motive := fun _ => List β)
      o (filterMap f xs) (fun b => cons b (filterMap f xs)))) (Nat.succ (length xs))) (f a)
      (Nat.le.step ih) (fun _ => Nat.succ_le_succ ih)) l

theorem filterMap_flatten {α : Type u} {β : Type v} {f : α → Option β} {L : List (List α)} :
    Eq (filterMap f (flatten L)) (flatten (map (filterMap f) L)) :=
  List.rec (motive := fun ls => Eq (filterMap f (flatten ls)) (flatten (map (filterMap f) ls))) Omega.rfl
    (fun xs _ ih => filterMap_append.trans (congrArg (List.append (filterMap f xs)) ih)) L

theorem filter_flatten {α : Type u} {p : α → Bool} {L : List (List α)} :
    Eq (filter p (flatten L)) (flatten (map (filter p) L)) :=
  List.rec (motive := fun ls => Eq (filter p (flatten ls)) (flatten (map (filter p) ls))) Omega.rfl
    (fun xs ls ih => (filter_append xs (flatten ls)).trans (congrArg (List.append (filter p xs)) ih)) L

theorem exists_mem_of_ne_nil {α : Type u} (l : List α) (h : Ne l nil) : Exists (fun x => Mem x l) :=
  List.casesOn (motive := fun xs => Ne xs nil → Exists (fun x => Mem x xs)) l
    (fun e => False.elim (e Omega.rfl)) (fun a xs _ => Exists.intro a (Mem.head xs)) h

theorem length_pos_of_mem {α : Type u} {a : α} {l : List α} : Mem a l → Nat.lt Nat.zero (length l) :=
  List.casesOn (motive := fun xs => Mem a xs → Nat.lt Nat.zero (length xs)) l
    (fun h => False.elim (not_mem_nil h)) (fun _ xs _ => Nat.succ_le_succ (Nat.zero_le (length xs)))

theorem length_pos_iff {α : Type u} {l : List α} : Iff (Nat.lt Nat.zero (length l)) (Ne l nil) :=
  List.casesOn (motive := fun xs => Iff (Nat.lt Nat.zero (length xs)) (Ne xs nil)) l
    (Iff.intro (fun h => False.elim (Nat.not_succ_le_zero Nat.zero h))
      (fun h => False.elim (h Omega.rfl)))
    (fun a xs => Iff.intro (fun _ => cons_ne_nil a xs) (fun _ => Nat.succ_le_succ (Nat.zero_le (length xs))))

theorem length_pos_iff_exists_mem {α : Type u} {l : List α} :
    Iff (Nat.lt Nat.zero (length l)) (Exists (fun a => Mem a l)) :=
  Iff.intro (fun h => exists_mem_of_ne_nil l (length_pos_iff.mp h))
    (fun h => h.elim (fun _ hm => length_pos_of_mem hm))

theorem length_eq_one_iff {α : Type u} {l : List α} :
    Iff (Eq (length l) (Nat.succ Nat.zero)) (Exists (fun a => Eq l (cons a nil))) :=
  Iff.intro (List.casesOn (motive := fun xs => Eq (length xs) (Nat.succ Nat.zero) →
      Exists (fun a => Eq xs (cons a nil))) l
    (fun e => False.elim (Nat.succ_ne_zero Nat.zero e.symm))
    (fun a _ h => Exists.intro a (congrArg (cons a) (eq_nil_of_length_eq_zero (Nat.succ.inj h)))))
    (fun h => h.elim (fun _ e => congrArg length e))

end Omega.List

public section
namespace Omega.absurd
export _root_.absurd (congr_simp)
end Omega.absurd
