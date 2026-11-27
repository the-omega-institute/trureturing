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

@[export omega_test_string_valid_bytes]
public def validBytes (b : Omega.ByteArray) : Bool := Omega.ByteArray.validateUTF8 b

@[export omega_test_string_get]
public def getAt (s : Omega.String) (i : Nat) : Omega.Char := Omega.String.Pos.Raw.get s ⟨i⟩

@[export omega_test_string_next]
public def nextAt (s : Omega.String) (i : Nat) : Nat := (Omega.String.Pos.Raw.next s ⟨i⟩).byteIdx

@[export omega_test_string_prev]
public def prevAt (s : Omega.String) (i : Nat) : Nat := (Omega.String.Pos.Raw.prev s ⟨i⟩).byteIdx

@[export omega_test_string_end]
public def endAt (s : Omega.String) (i : Nat) : Bool := Omega.String.Pos.Raw.atEnd s ⟨i⟩

@[export omega_test_string_valid_pos]
public def validAt (s : Omega.String) (i : Nat) : Bool := Omega.String.Pos.Raw.isValid s ⟨i⟩

@[export omega_test_string_push]
public def pushChar (s : Omega.String) (c : Omega.Char) : Omega.String := Omega.String.push s c

@[export omega_test_string_append]
public def appendText (a b : Omega.String) : Omega.String := Omega.String.append a b

@[export omega_test_string_length]
public def textLength (s : Omega.String) : Nat := Omega.String.Internal.length s

@[export omega_test_string_extract]
public def extractText (s : Omega.String) (a b : Nat) : Omega.String :=
  Omega.String.Internal.extract s ⟨a⟩ ⟨b⟩

@[export omega_test_string_utf8]
public def textUTF8 (s : Omega.String) : Omega.ByteArray := Omega.String.toUTF8 s
