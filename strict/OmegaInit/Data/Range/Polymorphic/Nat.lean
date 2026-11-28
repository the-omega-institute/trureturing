/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Data.Range.Polymorphic.UpwardEnumerable
public import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Lemmas

port_definition Std.PRange.instUpwardEnumerableNat with_native_code
attribute [instance] Omega.Std.PRange.instUpwardEnumerableNat

public theorem Omega.Std.PRange.instInfinitelyUpwardEnumerableNat :
    InfinitelyUpwardEnumerable Nat :=
  @InfinitelyUpwardEnumerable.mk Nat instUpwardEnumerableNat (fun _ => Omega.rfl)

public section
namespace Omega.Std.PRange
theorem instLawfulUpwardEnumerableNat : LawfulUpwardEnumerable Nat :=
  LawfulUpwardEnumerable.mk (fun a _ h eq => h.elim (fun n hn =>
    have same := (congrArg (fun x => Option.getD x a) hn).trans eq.symm
    have positive : Eq (Nat.succ n) Nat.zero := Nat.add_left_cancel same
    Nat.succ_ne_zero _ positive)) (fun _ => Omega.rfl) (fun _ _ => Omega.rfl)
end Omega.Std.PRange

attribute [instance] Omega.Std.PRange.instLawfulUpwardEnumerableNat
attribute [instance] Omega.Std.PRange.instInfinitelyUpwardEnumerableNat
