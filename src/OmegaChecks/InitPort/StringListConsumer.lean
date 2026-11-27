module
prelude
public import OmegaInit.Data.String.Basic

@[export omega_string_roundtrip]
public def roundTrip (s : Omega.String) : Omega.String := Omega.String.ofList (Omega.String.toList s)

@[export omega_string_scalars]
public def scalars (s : Omega.String) : Omega.List Omega.Char := Omega.String.toList s

@[export omega_string_bytes]
public def bytes (s : Omega.String) : Omega.Nat := Omega.String.utf8ByteSize s

@[export omega_test_string_raw]
public def raw (s : Omega.String) : Omega.ByteArray := Omega.String.toByteArray s

@[export omega_test_string_equal]
public def equal (a b : Omega.String) : Omega.Bool :=
  @Decidable.decide _ (Omega.String.decEq a b)

@[export omega_test_string_less]
public def less (a b : Omega.String) : Omega.Bool :=
  @Decidable.decide _ (Omega.String.decidableLT a b)

@[export omega_test_string_hash]
public def stringHash (s : Omega.String) : Omega.UInt64 := Omega.String.hash s

@[export omega_test_string_data]
public def stringData (s : Omega.String) : Omega.List Omega.Char := Omega.String.data s
