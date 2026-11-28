/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import OmegaInit.Grind.Module.Basic
public import OmegaInit.Data.Order.Classes

port_prop_record Lean.Grind.OrderedAdd
port_prop_record Lean.Grind.ExistsAddOfLT

namespace Omega.Lean.Grind.OrderedAdd
open Std AddCommMonoid
variable {M : Type u} [LE M] [IsPreorder M] [AddCommMonoid M] [OrderedAdd M]

public theorem add_le_right_iff {a b : M} (c : M) :
    Iff (LE.le a b) (LE.le (Add.add c a) (Add.add c b)) :=
  (add_le_left_iff c).trans (Iff.of_eq (congr (congrArg LE.le (add_comm a c)) (add_comm b c)))

end Omega.Lean.Grind.OrderedAdd

port_proof Lean.Grind.OrderedAdd.add_le_left
port_proof Lean.Grind.OrderedAdd.add_le_right
namespace Omega.Lean.Grind.OrderedAdd
open Std
variable {M : Type u} [LE M] [IsPreorder M] [AddCommMonoid M] [OrderedAdd M]

public theorem add_le_add {a b c d : M} (hab : LE.le a b) (hcd : LE.le c d) :
    LE.le (Add.add a c) (Add.add b d) :=
  IsPreorder.le_trans _ _ _ (add_le_right a hcd) (add_le_left hab d)

end Omega.Lean.Grind.OrderedAdd
