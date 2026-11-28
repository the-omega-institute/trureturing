/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Int.Basic
public import OmegaInit.Data.Nat.Bitwise.Basic

port_definition Int.not with_native_code
port_definition Int.instComplement with_native_code
port_definition Int.shiftRight.match_1 with_native_code
port_definition Int.shiftRight with_native_code
port_definition Int.instHShiftRightNat with_native_code
port_definition Int.shiftLeft with_native_code
port_definition Int.instHShiftLeftNat with_native_code

attribute [instance] Omega.Int.instComplement Omega.Int.instHShiftRightNat Omega.Int.instHShiftLeftNat
