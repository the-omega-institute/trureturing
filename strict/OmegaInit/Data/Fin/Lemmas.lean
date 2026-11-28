/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Fin.Basic

port_proof Fin.ext
port_proof Fin.val_cast by_reflexivity
port_proof Fin.val_natAdd by_reflexivity
port_proof Fin.coe_natAdd by_reflexivity
port_proof Fin.natAdd_mk by_reflexivity
port_proof Fin.natAdd_cast by_reflexivity
private theorem castZero {n n' : Nat} (i : Omega.Fin n) (h : Omega.Eq (Nat.add 0 n) n') :
    Omega.Eq (Omega.Fin.cast h (Omega.Fin.natAdd 0 i))
      (Omega.Fin.cast ((Omega.Nat.zero_add n).symm.trans h) i) :=
  Omega.Fin.eq_of_val_eq (Omega.Nat.zero_add i.val)

port_proof Fin.cast_natAdd_zero using castZero

/- Fin.natAdd_zero compares two functions. Their value projections reduce to
`fun i : Fin n => 0 + i.val` and `fun i => i.val`. Zero addition proves agreement
at each input. The original function equality is equivalent to equality of these
two projections for every bound. See OmegaChecks.InitInventory.FinAddition.
Specializing the definition of natAdd at zero would change the public reduction
of val_natAdd at a variable offset. -/
