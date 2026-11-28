/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import OmegaInit.Data.Option.Lemmas

port_proof Option.attachWith._proof_1
port_definition Option.attachWith.match_1 with_native_code
port_definition Option.attachWith with_native_code
port_proof Option.attach._proof_1
port_definition Option.attach with_native_code
port_definition Option.unattach with_native_code
port_proof Option.attach_none by_reflexivity
port_proof Option.attach_some by_reflexivity
port_proof Option.attachWith_none by_reflexivity
port_proof Option.unattach.eq_1 by_reflexivity

port_proof Option.attachWith.congr_simp
port_proof Option.unattach_none
port_proof Option.unattach_some

namespace Omega.Option

public theorem attach_map_val {α : Type u} {β : Type v} (o : Option α) (f : α → β) :
    Eq (o.attach.map (fun i => f (Subtype.val i))) (o.map f) :=
  Option.casesOn (motive := fun x =>
    Eq (x.attach.map (fun (i : Subtype (fun a => Eq x (some a))) => f i.val)) (x.map f))
    o rfl (fun _ => rfl)

public theorem attach_map_subtype_val {α : Type u} (o : Option α) : Eq (o.attach.map Subtype.val) o :=
  Option.casesOn (motive := fun x => Eq (x.attach.map Subtype.val) x) o rfl (fun _ => rfl)

public theorem isSome_attach {α : Type u} (o : Option α) : Eq o.attach.isSome o.isSome :=
  Option.casesOn (motive := fun x => Eq x.attach.isSome x.isSome) o rfl (fun _ => rfl)

public theorem isNone_attach {α : Type u} (o : Option α) : Eq o.attach.isNone o.isNone :=
  Option.casesOn (motive := fun x => Eq x.attach.isNone x.isNone) o
    (isNone_none.trans isNone_none.symm) (fun _ => isNone_some.trans isNone_some.symm)

public theorem isSome_unattach {α : Type u} {p : α → Prop} {o : Option (Subtype p)} :
    Eq o.unattach.isSome o.isSome :=
  Option.casesOn (motive := fun x => Eq x.unattach.isSome x.isSome) o rfl (fun _ => rfl)

public theorem isNone_unattach {α : Type u} {p : α → Prop} {o : Option (Subtype p)} :
    Eq o.unattach.isNone o.isNone :=
  Option.casesOn (motive := fun x => Eq x.unattach.isNone x.isNone) o
    (isNone_none.trans isNone_none.symm) (fun _ => isNone_some.trans isNone_some.symm)

public theorem unattach_attach {α : Type u} (o : Option α) : Eq o.attach.unattach o :=
  attach_map_subtype_val o

public theorem attachWith_map_subtype_val {α : Type u} {p : α → Prop}
    (o : Option α) (H : ∀ a, Eq o (some a) → p a) : Eq ((o.attachWith p H).map Subtype.val) o :=
  Option.casesOn (motive := fun x => ∀ (hx : ∀ a, Eq x (some a) → p a),
    Eq ((x.attachWith p hx).map Subtype.val) x)
    o (fun _ => rfl) (fun _ _ => rfl) H

public theorem unattach_attachWith {α : Type u} {p : α → Prop}
    {o : Option α} {H : ∀ a, Eq o (some a) → p a} : Eq (o.attachWith p H).unattach o :=
  attachWith_map_subtype_val o H

public theorem isSome_attachWith {α : Type u} {p : α → Prop}
    (o : Option α) (H : ∀ a, Eq o (some a) → p a) : Eq (o.attachWith p H).isSome o.isSome :=
  Option.casesOn (motive := fun x => ∀ (hx : ∀ a, Eq x (some a) → p a),
    Eq (x.attachWith p hx).isSome x.isSome)
    o (fun _ => rfl) (fun _ _ => rfl) H

public theorem isNone_attachWith {α : Type u} {p : α → Prop}
    (o : Option α) (H : ∀ a, Eq o (some a) → p a) : Eq (o.attachWith p H).isNone o.isNone :=
  Option.casesOn (motive := fun x => ∀ (hx : ∀ a, Eq x (some a) → p a),
    Eq (x.attachWith p hx).isNone x.isNone)
    o (fun _ => isNone_none.trans isNone_none.symm) (fun _ _ => isNone_some.trans isNone_some.symm) H

end Omega.Option
