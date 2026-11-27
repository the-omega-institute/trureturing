module

public import OmegaBuild.Commands
public import OmegaMath.Data.Nat
public import Mathlib.Data.Nat.Factorial.Basic

/-! A Mathlib-only consumer for backend scheduling and frozen dependency measurement. -/

compile_only_with_mathlib

namespace OmegaChecks.Portable

/-- A standard-library consumer whose input is the official interpretation of Omega naturals. -/
public def mathlibFactorial (n : Omega.Nat) : Nat := Nat.factorial n

end OmegaChecks.Portable
