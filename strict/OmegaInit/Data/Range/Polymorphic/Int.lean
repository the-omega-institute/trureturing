/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Data.Range.Polymorphic.UpwardEnumerable
public import OmegaInit.Data.Int.Basic
import OmegaInit.Data.Int.Lemmas

port_definition Std.PRange.instUpwardEnumerableInt with_native_code
attribute [instance] Omega.Std.PRange.instUpwardEnumerableInt

public theorem Omega.Std.PRange.instInfinitelyUpwardEnumerableInt :
    InfinitelyUpwardEnumerable Int :=
  @InfinitelyUpwardEnumerable.mk Int instUpwardEnumerableInt (fun _ => Omega.rfl)

public section
namespace Omega.Std.PRange
theorem instLawfulUpwardEnumerableInt : LawfulUpwardEnumerable Int :=
  LawfulUpwardEnumerable.mk (fun a _ h eq => h.elim (fun n hn =>
    have same := (congrArg (fun x => Option.getD x a) hn).trans eq.symm
    have positive : Eq (Int.ofNat (Nat.succ n)) (Int.ofNat 0) :=
      Int.add_left_cancel (same.trans (Int.add_zero a).symm)
    Nat.succ_ne_zero _ (congrArg Int.toNat positive)))
    (fun a => congrArg Option.some (Int.add_zero a))
    (fun n a => congrArg Option.some (Int.add_assoc a (Int.ofNat n) (Int.ofNat 1)).symm)
end Omega.Std.PRange

attribute [instance] Omega.Std.PRange.instLawfulUpwardEnumerableInt
attribute [instance] Omega.Std.PRange.instInfinitelyUpwardEnumerableInt
