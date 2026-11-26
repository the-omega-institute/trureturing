/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.List.Basic

port_proof List.isEmpty.eq_1 by_reflexivity
port_proof List.isEmpty.eq_2 by_reflexivity
