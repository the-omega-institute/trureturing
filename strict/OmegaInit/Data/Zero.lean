/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
module
prelude
public import OmegaInit.Coe

port_definition Zero.toOfNat0 with_native_code
port_definition Zero.ofOfNat0 with_native_code
port_definition One.toOfNat1 with_native_code
port_definition One.ofOfNat1 with_native_code

attribute [instance 300] Omega.Zero.toOfNat0
attribute [instance 200] Omega.Zero.ofOfNat0
attribute [instance 300] Omega.One.toOfNat1
attribute [instance 200] Omega.One.ofOfNat1

port_definition npowRec.match_1
port_definition npowRec._f
port_definition npowRec
port_structural_code npowRec on_arg 4
port_definition nsmulRec._f
port_definition nsmulRec
port_structural_code nsmulRec on_arg 4
