module
prelude
public import OmegaInit.Util

@[export omega_test_guarded_identity]
public def guardedIdentity {α : Type} (a b : α) (k : Unit → Omega.Bool)
    (onEqual : Eq a b → Eq (k ()) Omega.Bool.true) : Omega.Bool :=
  Omega.withPtrEq a b k onEqual
