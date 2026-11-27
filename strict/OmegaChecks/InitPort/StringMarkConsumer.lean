module
prelude
public import OmegaInit.Data.String.Defs

@[export omega_test_mark]
public def mark (s : Omega.String) : Omega.String := Omega.String.markLinear s

@[export omega_test_propagate]
public def propagate (s : Omega.String) (t : Omega.String) : Omega.String :=
  Omega.String.propagateMark s t

@[export omega_test_push_marked]
public def pushMarked (s : Omega.String) (c : Omega.Char) : Omega.String :=
  Omega.String.push s c
