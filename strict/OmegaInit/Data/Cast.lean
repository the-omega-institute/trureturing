/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module
prelude
public import OmegaInit.Coe

port_native_records NatCast
port_definition NatCast.noConfusionType
port_definition NatCast.noConfusion
port_definition NatCast.mk.noConfusion
port_definition NatCast.ctorIdx with_native_code
port_definition instNatCastNat with_native_code
port_definition Nat.cast with_native_code
port_definition instCoeTailNatOfNatCast with_native_code
port_definition instCoeHTCTNatOfNatCast with_native_code

attribute [instance] Omega.instNatCastNat Omega.instCoeTailNatOfNatCast Omega.instCoeHTCTNatOfNatCast
attribute [coe] Omega.Nat.cast
attribute [match_pattern] Omega.Nat.cast

public section
namespace Nat
export _root_.Omega.Nat (cast)
end Nat
