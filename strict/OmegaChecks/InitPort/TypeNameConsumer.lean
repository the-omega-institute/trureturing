module
prelude
public import OmegaInit.Dynamic

@[export omega_type_name_round_trip] public unsafe def roundTripName (n : Omega.Lean.Name) : Omega.Lean.Name :=
  @Omega.TypeName.typeName Omega.Nat (Omega.TypeName.mk Omega.Nat n)

@[export omega_type_name_nested] public def nestedName (n : Omega.Lean.Name) : Omega.Lean.Name :=
  Omega.Lean.Name.num n (Omega.Nat.succ Omega.Nat.zero)
