module
prelude
public import OmegaInit.Prelude

@[export omega_mixed_empty_string]
public def emptyString (_ : Omega.Bool) : Omega.String := Omega.String.ofList .nil

@[export omega_mixed_scalars]
public def scalarPair (a b : Omega.Nat) : Omega.String :=
  Omega.String.ofList (.cons (Omega.Char.ofNat a) (.cons (Omega.Char.ofNat b) .nil))
