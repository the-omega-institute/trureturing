/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

prelude
public import OmegaInit.Data.Zero
public import OmegaInit.Core

port_native_records NeZero
port_proof NeZero.ne
port_proof instNeZeroNatHAdd_1
attribute [instance] Omega.instNeZeroNatHAdd_1
