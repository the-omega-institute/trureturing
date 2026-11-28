/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Core

port_native_records Std.Slice
port_definition Std.Slice.noConfusionType
port_definition Std.Slice.noConfusion
port_definition Std.Slice.mk.noConfusion
port_definition Std.Slice.ctorIdx with_native_code
