module
prelude
public import OmegaInit.Dynamic

@[export omega_dynamic_pack_nat]
public unsafe def packNat (name : Omega.Lean.Name) (value : Omega.Nat) : Omega.Dynamic :=
  @Omega.Dynamic.mk Omega.Nat (Omega.TypeName.mk Omega.Nat name) value

@[export omega_dynamic_read_nat]
public unsafe def readNat (name : Omega.Lean.Name) (value : Omega.Dynamic) : Omega.Option Omega.Nat :=
  @Omega.Dynamic.get? Omega.Nat value (Omega.TypeName.mk Omega.Nat name)

@[export omega_dynamic_read_bool]
public unsafe def readBool (name : Omega.Lean.Name) (value : Omega.Dynamic) : Omega.Option Omega.Bool :=
  @Omega.Dynamic.get? Omega.Bool value (Omega.TypeName.mk Omega.Bool name)

@[noinline] private def applyName (f : Omega.Dynamic → Omega.Lean.Name) (d : Omega.Dynamic) := f d

@[export omega_dynamic_name]
public def storedName (d : Omega.Dynamic) := applyName Omega.Dynamic.typeName d
