module
prelude
public import OmegaInit.Control.Id
public import OmegaInit.Data.List.Control

@[export omega_test_list_search]
public def listSearch (all : Omega.Bool) (predicate : Nat → Omega.Bool) (xs : Omega.List Nat) : Omega.Bool :=
  match all with
  | .true  => Omega.List.allM (m := Omega.Id) predicate xs
  | .false => Omega.List.anyM (m := Omega.Id) predicate xs
