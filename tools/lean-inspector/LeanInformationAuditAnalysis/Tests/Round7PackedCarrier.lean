import Lean
namespace Round7PackedCarrier
structure Packet where
  carrier : Type
  value : carrier
  bit : Bool

def hidden (_ : Unit) (bit : Bool) : Packet :=
  ⟨PLift ((137 : Nat) = 137), ⟨rfl⟩, bit⟩
def clean (_ : Unit) (bit : Bool) : Packet := ⟨Nat, 0, bit⟩
end Round7PackedCarrier

namespace Round7PackedCarrier
def plain (_ : Unit) (bit : Bool) : Bool := bit
end Round7PackedCarrier
