module
prelude
public import OmegaMath.Data.Int
public import OmegaMathlib.Data.Nat.Fib.Basic

/-! Public consumers of the conjunction and Fibonacci interfaces. -/

namespace OmegaChecks.Portable.Common

public theorem projectLeft {p q : Prop} (h : Omega.And p q) : p :=
  Omega.And.left h

public theorem fibonacciRecurrence (n : Omega.Nat) :
    Omega.Eq (Omega.Nat.fib n.succ.succ)
      ((Omega.Nat.fib n).add (Omega.Nat.fib n.succ)) :=
  Omega.Nat.fib_add_two

public theorem natSquareMul (a k : Omega.Nat) :
    Omega.Eq ((a.mul k).mul (a.mul k)) ((a.mul a).mul (k.mul k)) :=
  a.square_mul k

public theorem intSquareMul (a k : Omega.Int) :
    Omega.Eq (a.mul k).square (a.square.mul k.square) :=
  a.square_mul k

public theorem intMaxAdd (a b c : Omega.Int) :
    Omega.Eq ((a.add c).max (b.add c)) ((Omega.Int.max a b).add c) :=
  a.max_add_common_right b c

end OmegaChecks.Portable.Common
