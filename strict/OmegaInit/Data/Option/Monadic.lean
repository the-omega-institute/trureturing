/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import OmegaInit.Data.Option.Instances
public import OmegaInit.Data.Option.Lemmas

port_proof Option.bindM_none by_reflexivity
port_proof Option.bindM_some by_reflexivity
port_proof Option.forM_eq_forM by_reflexivity
port_proof Option.forM_none by_reflexivity
port_proof Option.forM_some by_reflexivity
port_proof Option.forIn'_none by_reflexivity
port_proof Option.forIn_none by_reflexivity
port_proof Option.filterM_none by_reflexivity
port_proof Option.filterM_some by_reflexivity
