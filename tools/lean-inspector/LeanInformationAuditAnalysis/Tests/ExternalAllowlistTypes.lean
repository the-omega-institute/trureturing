import Lean

-- No protected imports: these are external-library type occurrences.
namespace ExternalAllowlistTypes

def typedRead (_ : PLift ((137 : Nat) = 137)) (bit : Bool) : Bool := bit
def predicate (_ : Unit) : Prop := (137 : Nat) = 137
structure PredicateRecord : Type where
  evidence : PLift (Exists predicate)
inductive PredicateBox where
  | mk (evidence : PredicateRecord) (bit : Bool) : PredicateBox

inductive ProofIndexed : ((137 : Nat) = 137) → Type where
  | mk (_ : Unit) (_ : Bool) : ProofIndexed rfl

end ExternalAllowlistTypes
