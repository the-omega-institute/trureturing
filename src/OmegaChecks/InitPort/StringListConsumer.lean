module
prelude
public import OmegaInit.Data.String.Basic

@[export omega_string_roundtrip]
public def roundTrip (s : Omega.String) : Omega.String := Omega.String.ofList (Omega.String.toList s)

@[export omega_string_scalars]
public def scalars (s : Omega.String) : Omega.List Omega.Char := Omega.String.toList s

@[export omega_string_bytes]
public def bytes (s : Omega.String) : Omega.Nat := Omega.String.utf8ByteSize s
