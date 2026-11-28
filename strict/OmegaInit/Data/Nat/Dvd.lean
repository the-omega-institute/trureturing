/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.SimpLemmas
import OmegaInit.Data.Nat.Basic

port_proof Nat.dvd_zero by_constructive_casts

public section
namespace Nat
export _root_.Omega.Nat (dvd_zero)
end Nat
