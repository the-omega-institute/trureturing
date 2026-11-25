module
public import Mathlib.Data.Nat.Fib.Basic
public import OmegaInit.Data.Nat.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Nat
export _root_.Nat (fib fib_add_two fib_le_fib_succ fib_lt_fib_succ fib_one fib_pos fib_two fib_zero)
end Omega.Nat
