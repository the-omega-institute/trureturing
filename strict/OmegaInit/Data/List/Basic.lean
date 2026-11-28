/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Prelude
import OmegaInit.Data.Nat.Basic

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

namespace Omega.List

def reverseAux {α : Type u} : List α → List α → List α := fun xs acc =>
  List.brecOn (motive := fun _ : List α => List α → List α) xs (fun ys below acc =>
    List.casesOn (motive := fun ys =>
        List.below (motive := fun _ : List α => List α → List α) ys → List α)
      ys (fun _ => acc) (fun a _ prior => prior.fst (cons a acc)) below) acc

end Omega.List

port_definition List.reverseAux.match_1 with_native_code
port_structural_code List.reverseAux on_arg 2

namespace Omega.List

def reverse {α : Type u} (as : List α) : List α := reverseAux as nil

theorem append_assoc {α : Type u} (as bs cs : List α) :
    Eq (List.append (List.append as bs) cs) (List.append as (List.append bs cs)) :=
  List.rec (motive := fun xs => Eq (List.append (List.append xs bs) cs) (List.append xs (List.append bs cs)))
    Omega.rfl (fun a _ ih => congrArg (cons a) ih) as

theorem length_nil {α : Type u} : Eq (length (nil : List α)) Nat.zero := Omega.rfl

theorem length_singleton {α : Type u} {a : α} :
    Eq (length (cons a nil)) (Nat.succ Nat.zero) := Omega.rfl

theorem length_cons {α : Type u} {a : α} {as : List α} :
    Eq (length (cons a as)) (Nat.succ (length as)) := Omega.rfl

theorem nil_append {α : Type u} (as : List α) : Eq (List.append nil as) as := Omega.rfl

theorem cons_append {α : Type u} {a : α} {as bs : List α} :
    Eq (List.append (cons a as) bs) (cons a (List.append as bs)) := Omega.rfl

theorem append_nil {α : Type u} (as : List α) : Eq (List.append as nil) as :=
  List.rec (motive := fun xs => Eq (List.append xs nil) xs)
    Omega.rfl (fun a _ ih => congrArg (cons a) ih) as

theorem length_append {α : Type u} {as bs : List α} :
    Eq (length (List.append as bs)) (Nat.add (length as) (length bs)) :=
  List.rec (motive := fun xs => Eq (length (List.append xs bs)) (Nat.add (length xs) (length bs)))
    (Nat.zero_add (length bs)).symm
    (fun _ xs ih => (congrArg Nat.succ ih).trans (Nat.succ_add (length xs) (length bs)).symm) as

theorem append_cons {α : Type u} (as : List α) (b : α) (bs : List α) :
    Eq (List.append as (cons b bs)) (List.append (List.append as (cons b nil)) bs) :=
  (append_assoc as (cons b nil) bs).symm

theorem reverse_nil {α : Type u} : Eq (reverse (nil : List α)) nil := Omega.rfl

theorem reverseAux_eq_append {α : Type u} {as bs : List α} :
    Eq (reverseAux as bs) (List.append (reverseAux as nil) bs) :=
  List.rec (motive := fun xs => ∀ ys, Eq (reverseAux xs ys) (List.append (reverseAux xs nil) ys))
    (fun _ => Omega.rfl)
    (fun a xs ih ys => (ih (cons a ys)).trans
      (((congrArg (fun ts => List.append ts ys) (ih (cons a nil))).trans
        (append_assoc (reverseAux xs nil) (cons a nil) ys)).symm))
    as bs

theorem reverse_cons {α : Type u} {a : α} {as : List α} :
    Eq (reverse (cons a as)) (List.append (reverse as) (cons a nil)) :=
  reverseAux_eq_append (as := as) (bs := cons a nil)

end Omega.List

port_proof List.reverseAux_nil by_reflexivity
port_proof List.reverseAux_cons by_reflexivity

namespace Omega.List

@[no_expose] def appendTR {α : Type u} (as bs : List α) : List α := List.append as bs
attribute [irreducible] appendTR

def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) (l : List α) : β :=
  List.brecOn (motive := fun _ : List α => β) l (fun xs below =>
    List.casesOn (motive := fun xs => List.below (motive := fun _ : List α => β) xs → β)
      xs (fun _ => init) (fun a _ prior => f a prior.fst) below)

def filter {α : Type u} (p : α → Bool) (l : List α) : List α :=
  List.brecOn (motive := fun _ : List α => List α) l (fun xs below =>
    List.casesOn (motive := fun xs => List.below (motive := fun _ : List α => List α) xs → List α)
      xs (fun _ => nil) (fun a _ prior =>
        Bool.casesOn (motive := fun _ => List α) (p a) prior.fst (cons a prior.fst)) below)

def filterMap {α : Type u} {β : Type v} (f : α → Option β) : List α → List β := fun l =>
  List.brecOn (motive := fun _ : List α => List β) l (fun xs below =>
    List.casesOn (motive := fun xs => List.below (motive := fun _ : List α => List β) xs → List β)
      xs (fun _ => nil) (fun a _ prior =>
        Option.casesOn (motive := fun _ => List β) (f a) prior.fst (fun b => cons b prior.fst)) below)

end Omega.List

port_proof List.foldr_nil by_reflexivity
port_proof List.foldr_cons by_reflexivity
port_proof List.filter_nil by_reflexivity
port_proof List.filterMap_nil by_reflexivity

namespace Omega.List

@[implicit_reducible] def replicate {α : Type u} : (n : Nat) → (a : α) → List α := fun n a =>
  Nat.brecOn (motive := fun _ => α → List α) n (fun i below a =>
    Nat.casesOn (motive := fun i => Nat.below (motive := fun _ => α → List α) i → List α)
      i (fun _ => nil) (fun _ prior => cons a (prior.fst a)) below) a

theorem replicate_zero {α : Type u} {a : α} : Eq (replicate Nat.zero a) nil := Omega.rfl

theorem replicate_succ {α : Type u} {a : α} {n : Nat} :
    Eq (replicate (Nat.succ n) a) (cons a (replicate n a)) := Omega.rfl

theorem length_replicate {α : Type u} {n : Nat} {a : α} : Eq (length (replicate n a)) n :=
  Nat.rec (motive := fun i => Eq (length (replicate i a)) i) Omega.rfl
    (fun _ ih => congrArg Nat.succ ih) n

theorem concat_eq_append {α : Type u} {as : List α} {a : α} :
    Eq (concat as a) (List.append as (cons a nil)) :=
  List.rec (motive := fun xs => Eq (concat xs a) (List.append xs (cons a nil))) Omega.rfl
    (fun x _ ih => congrArg (cons x) ih) as

theorem length_concat {α : Type u} {as : List α} {a : α} : Eq (length (concat as a)) (Nat.succ (length as)) :=
  (congrArg length concat_eq_append).trans (length_append.trans (Nat.add_one (length as)))

theorem flatMap_cons {α : Type u} {β : Type v} {x : α} {xs : List α} {f : α → List β} :
    Eq (flatMap f (cons x xs)) (List.append (f x) (flatMap f xs)) := Omega.rfl

theorem flatMap_append {α : Type u} {β : Type v} {xs ys : List α} {f : α → List β} :
    Eq (flatMap f (List.append xs ys)) (List.append (flatMap f xs) (flatMap f ys)) :=
  List.rec (motive := fun l => Eq (flatMap f (List.append l ys)) (List.append (flatMap f l) (flatMap f ys)))
    Omega.rfl (fun a as ih => (congrArg (List.append (f a)) ih).trans
      (append_assoc (f a) (flatMap f as) (flatMap f ys)).symm) xs

theorem length_add_eq_lengthTRAux {α : Type u} {as : List α} {n : Nat} :
    Eq (Nat.add (length as) n) (lengthTRAux as n) :=
  List.rec (motive := fun xs => ∀ k, Eq (Nat.add (length xs) k) (lengthTRAux xs k))
    Nat.zero_add (fun _ xs ih k => (Nat.succ_add (length xs) k).trans
      ((Nat.add_succ (length xs) k).symm.trans (ih (Nat.succ k)))) as n

theorem reverseAux_reverseAux {α : Type u} {as bs cs : List α} :
    Eq (reverseAux (reverseAux as bs) cs) (reverseAux bs (reverseAux (reverseAux as nil) cs)) :=
  List.rec (motive := fun xs => ∀ ys zs,
    Eq (reverseAux (reverseAux xs ys) zs) (reverseAux ys (reverseAux (reverseAux xs nil) zs)))
    (fun _ _ => Omega.rfl) (fun a _ ih ys zs => (ih (cons a ys) zs).trans
      (congrArg (reverseAux ys) (ih (cons a nil) zs).symm)) as bs cs

end Omega.List

port_proof List.map_nil by_reflexivity
port_proof List.map_cons by_reflexivity
port_proof List.flatten_nil by_reflexivity
port_proof List.flatMap_nil by_reflexivity
port_proof List.foldl_nil by_reflexivity
port_proof List.foldl_cons by_reflexivity

port_inductive List.Mem
port_definition List.instMembership with_native_code

namespace Omega.List

theorem mem_append_left {α : Type u} {a : α} {as : List α} (bs : List α) :
    Mem a as → Mem a (List.append as bs) :=
  fun h => Mem.rec (motive := fun xs _ => Mem a (List.append xs bs))
    (fun xs => Mem.head (List.append xs bs)) (fun b {_} _ ih => Mem.tail b ih) h

theorem mem_append_right {α : Type u} {b : α} (as : List α) {bs : List α} :
    Mem b bs → Mem b (List.append as bs) :=
  fun h => List.rec (motive := fun xs => Mem b (List.append xs bs)) h (fun x _ ih => Mem.tail x ih) as

end Omega.List

port_inductive List.Perm

namespace Omega.List
instance instAppend {α : Type u} : Append (List α) := Append.mk List.append
end Omega.List

attribute [instance] Omega.List.instMembership

port_proof List.append_eq by_reflexivity
port_proof List.flatten_cons by_reflexivity

port_definition List.eraseIdx.match_1
namespace Omega.List

def eraseIdx {α : Type u} : (l : List α) → (i : Nat) → List α := fun l i =>
  List.brecOn (motive := fun _ : List α => Nat → List α) l (fun x f index =>
    eraseIdx.match_1 (fun x _ =>
        List.below (motive := fun _ : List α => Nat → List α) x → List α) x index
      (fun _ _ => nil) (fun _ tail _ => tail) (fun a _ n below => cons a (below.fst n)) f) i

end Omega.List

port_proof List.eraseIdx_nil by_reflexivity
port_proof List.eraseIdx_cons_zero by_reflexivity

port_definition List.take.match_1
port_definition List.drop._f
port_definition List.drop
port_proof List.drop_nil

namespace Omega.List

public theorem drop_eq_nil_of_le {α : Type u} {as : List α} {i : Nat} (h : Nat.le (length as) i) :
    Eq (drop i as) nil :=
  List.rec (motive := fun l => ∀ k, Nat.le (length l) k → Eq (drop k l) nil)
    (fun k _ => drop_nil (i := k))
    (fun a l ih k => Nat.casesOn
      (motive := fun n => Nat.le (length (cons a l)) n → Eq (drop n (cons a l)) nil) k
      (fun bound => False.elim (Nat.not_succ_le_zero _ bound))
      (fun n bound => ih n (Nat.le_of_succ_le_succ bound))) as i h

end Omega.List
