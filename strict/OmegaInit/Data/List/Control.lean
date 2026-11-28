/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Control.Basic
public import OmegaInit.Data.List.Basic
public import OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Data.Nat.Bitwise.Basic

port_definition List.mapM.match_1 with_native_code
port_definition List.mapM.loop._f
port_definition List.mapM.loop
port_structural_code List.mapM.loop on_arg 6
port_definition List.mapM with_native_code
port_definition List.forM.match_1 with_native_code
port_definition List.forM._f
port_definition List.forM
port_structural_code List.forM on_arg 4
port_definition List.mapA._f
port_definition List.mapA
port_structural_code List.mapA on_arg 6
port_definition List.forA._f
port_definition List.forA
port_structural_code List.forA on_arg 4

port_definition List.zipWithM._sparseCasesOn_1
port_definition List.zipWithM.match_1 with_native_code
port_definition List.zipWithM.loop._f
port_definition List.zipWithM.loop
port_structural_code List.zipWithM.loop on_arg 7
port_definition List.zipWithM with_native_code
