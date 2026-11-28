/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Data.Option.Basic
public import OmegaInit.Data.Nat.Basic

port_native_records Std.PRange.UpwardEnumerable
port_definition Std.PRange.UpwardEnumerable.LT
port_prop_record Std.PRange.LawfulUpwardEnumerable
port_prop_record Std.PRange.InfinitelyUpwardEnumerable
port_proof Std.PRange.UpwardEnumerable.isSome_succ?
port_definition Std.PRange.UpwardEnumerable.succ with_native_code

private theorem allSuccessorsExist {α : Type u} [e : Omega.Std.PRange.UpwardEnumerable α]
    [l : Omega.Std.PRange.LawfulUpwardEnumerable α] [i : Omega.Std.PRange.InfinitelyUpwardEnumerable α]
    {n : Nat} {a : α} : Omega.Eq (Omega.Option.isSome (e.succMany? n a)) Bool.true :=
  Nat.rec (motive := fun k => Omega.Eq (Omega.Option.isSome (e.succMany? k a)) Bool.true)
    ((Omega.congrArg Omega.Option.isSome (l.succMany?_zero a)).trans Omega.rfl)
    (fun k ih => (Omega.congrArg Omega.Option.isSome (l.succMany?_add_one k a)).trans
      (Omega.Option.rec (motive := fun t => Omega.Eq (Omega.Option.isSome t) Bool.true →
          Omega.Eq (Omega.Option.isSome (Omega.Option.bind t e.succ?)) Bool.true)
        (fun h => Omega.False.elim (Omega.Bool.noConfusion h))
        (fun x _ => i.isSome_succ? x) (e.succMany? k a) ih)) n

port_proof Std.PRange.UpwardEnumerable.isSome_succMany? using allSuccessorsExist
port_definition Std.PRange.UpwardEnumerable.succMany with_native_code

public section
namespace Omega.Std.PRange
export _root_.Omega.Std.PRange.UpwardEnumerable (succ? succMany? isSome_succ? succ isSome_succMany? succMany)
end Omega.Std.PRange
