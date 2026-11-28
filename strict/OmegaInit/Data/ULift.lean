/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import OmegaInit.Core

port_definition instDecidableEqULift.decEq with_native_code
port_definition instDecidableEqULift with_native_code
port_proof instSubsingletonULift

attribute [instance] Omega.instDecidableEqULift Omega.instSubsingletonULift
