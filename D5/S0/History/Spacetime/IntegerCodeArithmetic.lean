/- GID: D5/S0/History/Spacetime/IntegerCodeArithmetic
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/IntegerCodeArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered integer arithmetic on the exact signed-magnitude HF codes. -/

import D5.S0.History.Spacetime.IntegerEncoding
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Order.MinMax

set_option autoImplicit false

namespace D5.S0.History.Spacetime.IntegerCodeArithmetic

open HFEncoding IntegerEncoding
noncomputable section

/-- The original structural signed-magnitude code subtype, without a new representation. -/
abbrev IntCode := {c : HF // IsIntCode c}

/-- Pull integer arithmetic back through the frozen decoder. -/
instance instCommRing : CommRing IntCode := int_code_equiv.symm.commRing

/-- Pull the integer order, including its maximum operation, back through the same decoder. -/
instance instLinearOrder : LinearOrder IntCode := by
  classical
  exact int_code_equiv.symm.linearOrder

/-- Forward map is `decodeInt`; inverse map is the original `int_code_equiv` encoder. -/
def decode_ring_equiv : IntCode ≃+* Int := int_code_equiv.symm.ringEquiv

/-- The order isomorphism has exactly the same forward and inverse functions as the ring one. -/
def decode_order_iso : IntCode ≃o Int where
  toEquiv := int_code_equiv.symm
  map_rel_iff' := Iff.rfl

/- These universal commuting laws supply the source-required arithmetic/order transport.
They are bind-only companions of the two representation bridges, not novelty claims. -/

@[simp] theorem encode_zero : int_code_equiv 0 = (0 : IntCode) :=
  map_zero decode_ring_equiv.symm

@[simp] theorem decode_zero : decodeInt (0 : IntCode).1 (0 : IntCode).2 = 0 :=
  map_zero decode_ring_equiv

@[simp] theorem encode_one : int_code_equiv 1 = (1 : IntCode) :=
  map_one decode_ring_equiv.symm

@[simp] theorem decode_one : decodeInt (1 : IntCode).1 (1 : IntCode).2 = 1 :=
  map_one decode_ring_equiv

@[simp] theorem encode_add (a b : Int) :
    int_code_equiv (a + b) = int_code_equiv a + int_code_equiv b :=
  map_add decode_ring_equiv.symm a b

@[simp] theorem decode_add (a b : IntCode) :
    decodeInt (a + b).1 (a + b).2 = decodeInt a.1 a.2 + decodeInt b.1 b.2 :=
  map_add decode_ring_equiv a b

@[simp] theorem encode_mul (a b : Int) :
    int_code_equiv (a * b) = int_code_equiv a * int_code_equiv b :=
  map_mul decode_ring_equiv.symm a b

@[simp] theorem decode_mul (a b : IntCode) :
    decodeInt (a * b).1 (a * b).2 = decodeInt a.1 a.2 * decodeInt b.1 b.2 :=
  map_mul decode_ring_equiv a b

@[simp] theorem encode_neg (a : Int) : int_code_equiv (-a) = -int_code_equiv a :=
  map_neg decode_ring_equiv.symm a

@[simp] theorem decode_neg (a : IntCode) :
    decodeInt (-a).1 (-a).2 = -decodeInt a.1 a.2 :=
  map_neg decode_ring_equiv a

@[simp] theorem encode_sub (a b : Int) :
    int_code_equiv (a - b) = int_code_equiv a - int_code_equiv b :=
  map_sub decode_ring_equiv.symm a b

@[simp] theorem decode_sub (a b : IntCode) :
    decodeInt (a - b).1 (a - b).2 = decodeInt a.1 a.2 - decodeInt b.1 b.2 :=
  map_sub decode_ring_equiv a b

@[simp] theorem encode_le (a b : Int) :
    int_code_equiv a ≤ int_code_equiv b ↔ a ≤ b :=
  decode_order_iso.symm.le_iff_le

@[simp] theorem decode_le (a b : IntCode) :
    decodeInt a.1 a.2 ≤ decodeInt b.1 b.2 ↔ a ≤ b :=
  decode_order_iso.le_iff_le

@[simp] theorem encode_lt (a b : Int) :
    int_code_equiv a < int_code_equiv b ↔ a < b :=
  decode_order_iso.symm.lt_iff_lt

@[simp] theorem decode_lt (a b : IntCode) :
    decodeInt a.1 a.2 < decodeInt b.1 b.2 ↔ a < b :=
  decode_order_iso.lt_iff_lt

@[simp] theorem encode_max (a b : Int) :
    int_code_equiv (max a b) = max (int_code_equiv a) (int_code_equiv b) :=
  decode_order_iso.symm.monotone.map_max

@[simp] theorem decode_max (a b : IntCode) :
    decodeInt (max a b).1 (max a b).2 = max (decodeInt a.1 a.2) (decodeInt b.1 b.2) :=
  decode_order_iso.monotone.map_max

/-- Generic ordered-ring transfer consumes the proved arithmetic and order commuting laws. -/
instance instIsStrictOrderedRing : IsStrictOrderedRing IntCode :=
  Function.Injective.isStrictOrderedRing (fun a : IntCode => decodeInt a.1 a.2)
    decode_zero decode_one decode_add decode_mul (fun {_ _} => decode_le _ _)
    (fun {_ _} => decode_lt _ _)

/-- The generated-event time expression commutes with the literal integer encoder. -/
theorem encode_max_add_one (a b : Int) :
    int_code_equiv (max a b + 1) = max (int_code_equiv a) (int_code_equiv b) + 1 := by
  rw [encode_add, encode_max, encode_one]

/-- Decoding coded parent times followed by maximum and successor gives the standard time. -/
theorem decode_max_add_one (a b : IntCode) :
    decodeInt (max a b + 1).1 (max a b + 1).2 =
      max (decodeInt a.1 a.2) (decodeInt b.1 b.2) + 1 := by
  rw [decode_add, decode_max, decode_one]

end
end D5.S0.History.Spacetime.IntegerCodeArithmetic
