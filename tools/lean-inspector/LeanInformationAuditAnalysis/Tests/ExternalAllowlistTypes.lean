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

def hiddenRelation (_ _ : Unit) : Prop := (137 : Nat) = 137
inductive QuotientBox where
  | mk (_ : Quot hiddenRelation) (_ : Bool) : QuotientBox
def cleanRelation (x y : Unit) : Prop := x = y
inductive CleanQuotientBox where
  | mk (_ : Quot cleanRelation) (_ : Bool) : CleanQuotientBox

def callback (_ : (137 : Nat) = 137) : Bool := true
inductive HiddenIndex : (((137 : Nat) = 137) → Bool) → Type where
  | mk : HiddenIndex callback
structure IndexRecord where
  token : HiddenIndex callback
inductive IndexBox where
  | mk (_ : IndexRecord) (_ : Bool) : IndexBox

structure IndexedCarrier (n : Nat) where
  Carrier : Type
  evidence : n = n
def unitCarrier (n : Nat) : IndexedCarrier n := ⟨Unit, rfl⟩
inductive SpecializedProjectionBox where
  | mk {f : (n : Nat) → IndexedCarrier n} (_ : (f 137).Carrier) (_ : Bool) :
      SpecializedProjectionBox

end ExternalAllowlistTypes

namespace ExternalAllowlistTypes

class UnknownEvidence : Type where
  proof : (138 : Nat) = 138
instance : Subsingleton UnknownEvidence := ⟨by intro a b; cases a; cases b; rfl⟩

def valuedUnknown [UnknownEvidence] (bit : Bool) : Bool := bit

inductive ValuelessUnknownOutput where
  | mk [UnknownEvidence] (bit : Bool) : ValuelessUnknownOutput

end ExternalAllowlistTypes
