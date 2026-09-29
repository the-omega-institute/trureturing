import Lean

namespace WitnessCarriers

def hiddenProduct (_ : Unit) (state : Bool) : PProd Type Bool :=
  ⟨PLift ((137 : Nat) = 137), state⟩
def cleanProduct (_ : Unit) (state : Bool) : PProd Type Bool := ⟨Nat, state⟩

structure PredicatePacket where
  statement : Prop
  proof : statement
  bit : Bool

def hiddenPredicate (_ : Unit) (state : Bool) : PredicatePacket :=
  ⟨(137 : Nat) = 137, rfl, state⟩

structure FamilyPacket where
  family : Unit → Type
  value : family ()
  bit : Bool

def hiddenFamily (_ : Unit) (state : Bool) : FamilyPacket :=
  ⟨fun _ => PLift ((137 : Nat) = 137), ⟨rfl⟩, state⟩

def hiddenStatements (_ : Unit) (state : Bool) : List Prop :=
  [if state then (137 : Nat) = 137 else False]
def cleanStatements (_ : Unit) (state : Bool) : List Prop :=
  [if state then True else False]

end WitnessCarriers
