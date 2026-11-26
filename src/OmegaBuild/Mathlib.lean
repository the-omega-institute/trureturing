module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.RelClasses
public import OmegaMathlib.Data.Nat.Choose.Basic
public import OmegaMathlib.Data.Nat.Fib.Basic
public import OmegaMathlib.Data.Nat.Prime.Defs
public import OmegaMathlib.Logic.Function.Basic
public import OmegaMathlib.Logic.Function.Defs
public import OmegaMathlib.Order.RelClasses
meta import OmegaBuild.Commands.Origin

/-! Standard Mathlib names for mixed native and Omega consumers. -/

run_cmd OmegaBuild.exportNativePorts
