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


namespace CorrectnessExternalRound4

structure StatementResult where
  evidence : PLift ((137 : Nat) = 137)
  bit : Bool

def valuedResult (_ : Unit) (bit : Bool) : StatementResult := ⟨⟨rfl⟩, bit⟩

structure CleanResult where
  evidence : PLift ((138 : Nat) = 138)
  bit : Bool

def cleanResult (_ : Unit) (bit : Bool) : CleanResult := ⟨⟨rfl⟩, bit⟩

end CorrectnessExternalRound4

namespace NominalFieldFixtures
structure ProofResult where
  evidence : (137 : Nat) = 137
  bit : Bool
def proofResult (_ : Unit) (bit : Bool) : ProofResult := ⟨rfl, bit⟩
structure CleanProofResult where
  evidence : (138 : Nat) = 138
  bit : Bool
def cleanProofResult (_ : Unit) (bit : Bool) : CleanProofResult := ⟨rfl, bit⟩
inductive InstanceResult where
  | mk [Decidable ((137 : Nat) = 137)] (bit : Bool) : InstanceResult
def instanceResult (_ : Unit) (bit : Bool) : InstanceResult := .mk bit
inductive CleanInstanceResult where
  | mk [Decidable ((138 : Nat) = 138)] (bit : Bool) : CleanInstanceResult
def cleanInstanceResult (_ : Unit) (bit : Bool) : CleanInstanceResult := .mk bit
universe u
structure UniverseResult where
  evidence : ∀ α : Sort u, α = α
  bit : Bool
def universeResult (_ : Unit) (bit : Bool) : UniverseResult.{u} := ⟨fun _ => rfl, bit⟩
end NominalFieldFixtures

namespace NominalFieldFixtures
def listedClassResult (_ : Unit) (_ : Bool) : PLift (Subsingleton Unit) := ⟨inferInstance⟩
def cleanListedClassResult (_ : Unit) (_ : Bool) : PLift (Subsingleton (Fin 1)) := ⟨inferInstance⟩
end NominalFieldFixtures

namespace NominalFieldFixtures
inductive IndexedResult : Nat → Type where
  | zero : IndexedResult 0
  | mk (n : Nat) (evidence : n = 137) (bit : Bool) : IndexedResult n
def indexedResult (_ : Unit) (bit : Bool) : IndexedResult 137 := .mk 137 rfl bit
inductive CleanIndexedResult : Nat → Type where
  | zero : CleanIndexedResult 0
  | mk (n : Nat) (evidence : n = 138) (bit : Bool) : CleanIndexedResult n
def cleanIndexedResult (_ : Unit) (bit : Bool) : CleanIndexedResult 138 := .mk 138 rfl bit
end NominalFieldFixtures

namespace NominalFieldFixtures
inductive UniformIndexedResult : Nat → Type where
  | mk (n : Nat) (evidence : n = 137) (bit : Bool) : UniformIndexedResult n
inductive RecursiveIndexedResult : Nat → Type where
  | zero : RecursiveIndexedResult 0
  | mk (n : Nat) (next : Option (RecursiveIndexedResult 138))
      (evidence : n = n) (bit : Bool) : RecursiveIndexedResult n
def recursiveIndexedResult (_ : Unit) (bit : Bool) : RecursiveIndexedResult 137 :=
  .mk 137 (some (.mk 138 none rfl bit)) rfl bit
inductive CleanRecursiveIndexedResult : Nat → Type where
  | zero : CleanRecursiveIndexedResult 0
  | mk (n : Nat) (next : Option (CleanRecursiveIndexedResult 139))
      (evidence : n = n) (bit : Bool) : CleanRecursiveIndexedResult n
def cleanRecursiveIndexedResult (_ : Unit) (bit : Bool) : CleanRecursiveIndexedResult 137 :=
  .mk 137 (some (.mk 139 none rfl bit)) rfl bit
end NominalFieldFixtures

namespace NominalFieldFixtures
inductive IndexSelfResult : Nat → Type where
  | zero : IndexSelfResult 0
  | mk (n : Nat) (evidence : n = n) (bit : Bool) : IndexSelfResult n
def indexSelfBy (n : Nat) (_ : Unit) (bit : Bool) : IndexSelfResult n := .mk n rfl bit
end NominalFieldFixtures
