import Lean
namespace AliasSortCarriers

def CarrierKind : Type 1 := Type
def PropositionKind : Type := Prop
def FamilyKind : Type 1 := Unit → Type
structure TypePacket where
  carrier : CarrierKind
  bit : Bool
structure PropPacket where
  proposition : PropositionKind
  bit : Bool
structure FamilyPacket where
  family : FamilyKind
  bit : Bool

def typeHidden (_ : Unit) (state : Bool) : TypePacket := ⟨PLift ((137 : Nat) = 137), state⟩
def typeClean (_ : Unit) (state : Bool) : TypePacket := ⟨Nat, state⟩
def propHidden (_ : Unit) (state : Bool) : PropPacket := ⟨(137 : Nat) = 137, state⟩
def propClean (_ : Unit) (state : Bool) : PropPacket := ⟨True, state⟩
def familyHidden (_ : Unit) (state : Bool) : FamilyPacket := ⟨fun _ => PLift ((137 : Nat) = 137), state⟩
def familyClean (_ : Unit) (state : Bool) : FamilyPacket := ⟨fun _ => Nat, state⟩
def plain (_ : Unit) (state : Bool) : Bool := state
end AliasSortCarriers
