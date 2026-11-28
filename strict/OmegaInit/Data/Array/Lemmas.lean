/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module
prelude
public import OmegaInit.Data.Array.Basic
public import OmegaInit.Core
import OmegaInit.Data.Array.Bootstrap
import OmegaInit.Data.List.Lemmas
import all OmegaInit.Data.Array.Basic

noncomputable section

@[expose] public section

namespace Omega.Array

attribute [local semireducible] Array.eraseIdxIfInBounds

theorem toList_inj {α : Type u} {xs ys : Array α} :
    Iff (Eq (Array.toList xs) (Array.toList ys)) (Eq xs ys) :=
  Iff.intro ext' (congrArg Array.toList)

theorem toList_eq_nil_iff {α : Type u} {xs : Array α} :
    Iff (Eq (Array.toList xs) List.nil) (Eq xs Array.empty) :=
  toList_inj

set_option relaxedAutoImplicit true in
theorem eq_empty_of_size_eq_zero (h : Eq (Array.size xs) Nat.zero) :
    Eq xs Array.empty := ext' (List.eq_nil_of_length_eq_zero h)

set_option relaxedAutoImplicit true in
theorem size_eq_zero_iff : Iff (Eq (Array.size xs) Nat.zero) (Eq xs Array.empty) :=
  Iff.intro eq_empty_of_size_eq_zero (congrArg Array.size)

set_option relaxedAutoImplicit true in
theorem eq_empty_iff_size_eq_zero : Iff (Eq xs Array.empty) (Eq (Array.size xs) Nat.zero) :=
  size_eq_zero_iff.symm

theorem toList_eraseIdxIfInBounds {α : Type u} {xs : Array α} {i : Nat} :
    Eq (Array.toList (Array.eraseIdxIfInBounds xs i)) (List.eraseIdx (Array.toList xs) i) := Omega.rfl

private theorem mapSection {α : Type u} {β : Type v} (pack : α → β) (unpack : β → α)
    (h : ∀ x, Eq (pack (unpack x)) x) (xs : List β) :
    Eq (List.map pack (List.map unpack xs)) xs := List.map_map.trans (List.map_id'' h xs)

theorem array₂_induction {α : Type u} (P : Array (Array α) → Prop)
    (of : ∀ (xss : List (List α)), P (List.toArray (List.map List.toArray xss)))
    (xss : Array (Array α)) : P xss :=
  let roundtrip := mapSection List.toArray Array.toList (fun _ => Omega.rfl) (Array.toList xss)
  Eq.subst (motive := P) (congrArg List.toArray roundtrip) (of (List.map Array.toList (Array.toList xss)))

theorem array₃_induction {α : Type u} (P : Array (Array (Array α)) → Prop)
    (of : ∀ (xss : List (List (List α))),
      P (List.toArray (List.map List.toArray (List.map (List.map List.toArray) xss))))
    (xss : Array (Array (Array α))) : P xss :=
  array₂_induction P (fun lists =>
    let roundtrip := mapSection (List.map List.toArray) (List.map Array.toList)
      (mapSection List.toArray Array.toList (fun _ => Omega.rfl)) lists
    Eq.subst (motive := fun ys => P (List.toArray (List.map List.toArray ys))) roundtrip
      (of (List.map (List.map Array.toList) lists))) xss

end Omega.Array

port_proof Array.length_toList by_reflexivity
port_proof Array.singleton_eq_toArray_singleton by_reflexivity

port_proof Option.getD.eq_1 by_reflexivity
port_proof Option.getD.eq_2 by_reflexivity

port_alternative_proof Array.toList_map from OmegaChecks.InitPort.Alternatives.MonadicLists
port_alternative_proof Array.size_map from OmegaChecks.InitPort.Alternatives.MonadicLists
port_alternative_proof Array.map_push from OmegaChecks.InitPort.Alternatives.MonadicLists
port_alternative_proof List.map_toArray from OmegaChecks.InitPort.Alternatives.MonadicLists
port_alternative_proof Array.map_id'' from OmegaChecks.InitPort.Alternatives.MonadicLists
port_proof Array.map_empty by_reflexivity
port_alternative_proof Array.map_eq_empty_iff from OmegaChecks.InitPort.Alternatives.MonadicLists
port_proof Array.eq_empty_of_map_eq_empty

namespace Omega.Array

public theorem map_id {α : Type u} (xs : Array α) : Eq (map id xs) xs :=
  map_id'' (fun _ => Omega.rfl) xs

public theorem map_map {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {as : Array α} :
    Eq (map g (map f as)) (map (fun x => g (f x)) as) :=
  ext' (toList_map.trans ((congrArg (List.map g) toList_map).trans (List.map_map.trans toList_map.symm)))

public theorem size_append {α : Type u} {xs ys : Array α} :
    Eq (size (Array.append xs ys)) (Nat.add (size xs) (size ys)) :=
  (congrArg List.length toList_append).trans List.length_append

public theorem map_append {α : Type u} {β : Type v} {f : α → β} {xs ys : Array α} :
    Eq (map f (Array.append xs ys)) (Array.append (map f xs) (map f ys)) :=
  let right := congrArg (List.append (List.map f xs.toList)) (toList_map (xs := ys) (f := f)).symm
  let left := congrArg (fun l => List.append l (map f ys).toList) (toList_map (xs := xs) (f := f)).symm
  ext' (toList_map.trans ((congrArg (List.map f) toList_append).trans
    (List.map_append.trans (right.trans (left.trans toList_append.symm)))))

public theorem toArray_eq_append_iff {α : Type u} {xs : List α} {as bs : Array α} :
    Iff (Eq (List.toArray xs) (Array.append as bs)) (Eq xs (List.append as.toList bs.toList)) :=
  Iff.intro (fun h => (congrArg Array.toList h).trans toList_append) (fun h => ext' (h.trans toList_append.symm))

public theorem append_eq_toArray_iff {α : Type u} {xs ys : Array α} {as : List α} :
    Iff (Eq (Array.append xs ys) (List.toArray as)) (Eq (List.append xs.toList ys.toList) as) :=
  Iff.intro (fun h => toList_append.symm.trans (congrArg Array.toList h)) (fun h => ext' (toList_append.trans h))

public theorem append_eq_empty_iff {α : Type u} {xs ys : Array α} :
    Iff (Eq (Array.append xs ys) Array.empty) (And (Eq xs Array.empty) (Eq ys Array.empty)) :=
  Iff.intro (fun h =>
    let e := List.append_eq_nil_iff.mp (toList_append.symm.trans (congrArg Array.toList h))
    And.intro (ext' e.left) (ext' e.right))
    (fun h => ext' (toList_append.trans (List.append_eq_nil_iff.mpr (And.intro (congrArg Array.toList h.left)
      (congrArg Array.toList h.right)))))

public theorem empty_eq_append_iff {α : Type u} {xs ys : Array α} :
    Iff (Eq Array.empty (Array.append xs ys)) (And (Eq xs Array.empty) (Eq ys Array.empty)) :=
  Iff.intro (fun h => append_eq_empty_iff.mp h.symm) (fun h => (append_eq_empty_iff.mpr h).symm)

end Omega.Array

port_proof Array.map_singleton by_reflexivity
port_proof Array.map_id' using Omega.Array.map_id


/- Open monadic searches. Array.findSomeRevM?_eq_findSomeM?_reverse is equivalent to
List.findSomeM?_toArray. Array.findRevM?_eq_findM?_reverse is equivalent to
List.findM?_toArray given List.findRevM?_toArray. That premise is equivalent to
List.findM?_eq_findSomeM?, which changes the Boolean branch into a search for
a tagged option. ReverseSearch.optionIff, boolIff and predicateIff prove these
relations using the ported reverse search and the involution on lists. -/
