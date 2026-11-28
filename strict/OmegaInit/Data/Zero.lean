/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
module

prelude
public import OmegaInit.Coe

port_definition Zero.ofOfNat0 with_native_code
port_definition Zero.toOfNat0 with_native_code

attribute [instance 300] Omega.Zero.toOfNat0
attribute [instance 200] Omega.Zero.ofOfNat0
