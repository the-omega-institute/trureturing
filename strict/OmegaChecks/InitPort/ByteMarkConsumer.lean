module
prelude
public import OmegaInit.Data.String.Defs

@[export omega_test_byte_mark]
public def byteMark (a : Omega.ByteArray) := Omega.ByteArray.markLinear a

@[export omega_test_byte_propagate]
public def bytePropagate (a b : Omega.ByteArray) := Omega.ByteArray.propagateMark a b

@[export omega_test_byte_push]
public def bytePush (a : Omega.ByteArray) (b : Omega.UInt8) := Omega.ByteArray.push a b

@[export omega_test_byte_set]
public def byteSet (a : Omega.ByteArray) (i : Nat) (b : Omega.UInt8) := Omega.ByteArray.set! a i b

@[export omega_test_byte_copy]
public def byteCopy (src dst : Omega.ByteArray) (length : Nat) :=
  Omega.ByteArray.copySlice src 0 dst 0 length Bool.true

@[export omega_test_bytes_of_string]
public def bytesOfString (s : Omega.String) := Omega.String.toUTF8 s
