/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.List.Basic
import OmegaInit.Data.Nat.Basic

port_native_records GetElem
port_definition Array.instGetElemNatLtSize

port_definition List.instGetElemNatLtLength
port_definition List.getElem_cons_drop._f
port_proof List.getElem_cons_drop
