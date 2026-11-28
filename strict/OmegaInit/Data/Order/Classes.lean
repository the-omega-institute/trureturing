/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Core

port_native_records Std.IsPreorder, Std.IsPartialOrder, Std.IsLinearPreorder, Std.IsLinearOrder
port_proof Std.IsLinearOrder.toIsLinearPreorder
port_native_records Std.LawfulOrderLT, Std.LawfulOrderBEq
port_native_records Std.MinEqOr, Std.LawfulOrderInf, Std.LawfulOrderMin, Std.LawfulOrderLeftLeaningMin
port_proof Std.MinEqOr.elim
port_native_records Std.MaxEqOr, Std.LawfulOrderSup, Std.LawfulOrderMax, Std.LawfulOrderLeftLeaningMax
port_proof Std.MaxEqOr.elim

attribute [instance] Omega.Std.IsPartialOrder.toIsPreorder Omega.Std.IsLinearPreorder.toIsPreorder
attribute [instance] Omega.Std.IsLinearOrder.toIsPartialOrder Omega.Std.IsLinearOrder.toIsLinearPreorder
attribute [instance] Omega.Std.LawfulOrderMin.toMinEqOr Omega.Std.LawfulOrderMin.toLawfulOrderInf
attribute [instance] Omega.Std.LawfulOrderMax.toMaxEqOr Omega.Std.LawfulOrderMax.toLawfulOrderSup
