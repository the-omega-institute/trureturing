/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Control.Id
public import OmegaInit.Core

port_proof Id.ext by_reflexivity
port_proof Id.ext_iff by_reflexivity
port_proof Function.const.eq_1 by_reflexivity
