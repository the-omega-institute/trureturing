/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Option.Basic

port_proof ReaderT.run_mk by_reflexivity
port_proof Option.elim.eq_1 by_reflexivity
port_proof Option.elim.eq_2 by_reflexivity
port_proof Option.map.eq_1 by_reflexivity
port_proof Option.map.eq_2 by_reflexivity
