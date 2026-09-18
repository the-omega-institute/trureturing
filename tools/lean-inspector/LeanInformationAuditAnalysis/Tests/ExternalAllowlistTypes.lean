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


namespace CorrectnessExternalRound5

inductive DirectIndexed : Nat → Type where
  | zero : DirectIndexed 0
  | mk (n : Nat) (proof : n = n) (bit : Bool) : DirectIndexed n

def directRead (_ : Unit) (bit : Bool) : DirectIndexed 137 := .mk 137 rfl bit

inductive IdentityIndexed : Nat → Type where
  | zero : IdentityIndexed 0
  | mk (n : Nat) (proof : n = n) (bit : Bool) : IdentityIndexed (id n)

def identityRead (_ : Unit) (bit : Bool) : IdentityIndexed 137 := .mk 137 rfl bit
def cleanIdentityRead (_ : Unit) (bit : Bool) : IdentityIndexed 139 := .mk 139 rfl bit

inductive SuccessorIndexed : Nat → Type where
  | zero : SuccessorIndexed 0
  | mk (n : Nat) (proof : n = n) (bit : Bool) : SuccessorIndexed (Nat.succ n)

def successorRead (_ : Unit) (bit : Bool) : SuccessorIndexed 138 := .mk 137 rfl bit
def cleanSuccessorRead (_ : Unit) (bit : Bool) : SuccessorIndexed 140 := .mk 139 rfl bit

end CorrectnessExternalRound5


namespace ReviewTestsA7External

structure NestedResult where
  inner : CorrectnessExternalRound4.StatementResult
  bit : Bool

def nestedResult (_ : Unit) (bit : Bool) : NestedResult :=
  ⟨⟨⟨rfl⟩, bit⟩, bit⟩

structure CleanNestedResult where
  inner : CorrectnessExternalRound4.CleanResult
  bit : Bool

def cleanNestedResult (_ : Unit) (bit : Bool) : CleanNestedResult :=
  ⟨⟨⟨rfl⟩, bit⟩, bit⟩

structure InstanceResult where
  [witness : Inhabited CorrectnessExternalRound4.StatementResult]
  bit : Bool

def instanceResult (_ : Unit) (bit : Bool) : InstanceResult :=
  @InstanceResult.mk ⟨⟨⟨rfl⟩, bit⟩⟩ bit

structure CleanInstanceResult where
  [witness : Inhabited CorrectnessExternalRound4.CleanResult]
  bit : Bool

def cleanInstanceResult (_ : Unit) (bit : Bool) : CleanInstanceResult :=
  @CleanInstanceResult.mk ⟨⟨⟨rfl⟩, bit⟩⟩ bit

end ReviewTestsA7External

namespace NumericMetadataFixtures
def boundedRead (_ : Unit) (_ : Bool) : Fin 256 := ⟨0, Nat.zero_lt_succ 255⟩
end NumericMetadataFixtures

namespace ListMetadataFixtures
structure UniqueRange where
  count : Nat
  proof : (List.range count).Nodup
  bit : Bool
def uniqueRead (_ : Unit) (bit : Bool) : UniqueRange := ⟨0, by simp, bit⟩
structure PredicatePairwise where
  proof : List.Pairwise (fun a _ : Nat => ∃ k : Nat, k = a) [137, 0]
  bit : Bool
def predicateRead (_ : Unit) (bit : Bool) : PredicatePairwise :=
  ⟨.cons (by intro b hb; exact ⟨137, rfl⟩) (.cons (by simp) .nil), bit⟩
structure UniqueLiteral where
  proof : ([137, 0] : List Nat).Nodup
  bit : Bool
def literalRead (_ : Unit) (bit : Bool) : UniqueLiteral := ⟨by decide, bit⟩
end ListMetadataFixtures

namespace ListMetadataFixtures
def propositionList : List Prop := [∃ k : Nat, k = 137, False]
structure PropositionUnique where
  proof : propositionList.Nodup
  bit : Bool
def propositionRead (_ : Unit) (bit : Bool) : PropositionUnique :=
  ⟨.cons (by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro h
    exact Eq.mp h ⟨137, rfl⟩) (.cons (by simp) .nil), bit⟩
end ListMetadataFixtures

namespace ListMetadataFixtures
def mapProofRead {α β : Type} (f : α → β) (l : List α)
    (_ : (l.map f).Nodup) (_ : Unit) (bit : Bool) : Bool := bit
inductive TypeIndexed : Type → Type 1 where
  | mk (proof : propositionList.Nodup) (bit : Bool) : TypeIndexed Prop
def indexedRead (α : Type) (h : α = Prop) (_ : Unit) (bit : Bool) : TypeIndexed α :=
  h.symm ▸ TypeIndexed.mk (propositionRead () bit).proof bit
structure LetPropositionUnique where
  proof : (let carrier : Type := Prop
           let xs : List carrier := propositionList
           List.Pairwise (fun a b : carrier => a ≠ b) xs)
  bit : Bool
def letPropositionRead (_ : Unit) (bit : Bool) : LetPropositionUnique :=
  ⟨(propositionRead () bit).proof, bit⟩
end ListMetadataFixtures

namespace ListMetadataFixtures
inductive Choice where | left | right deriving DecidableEq
def enumMemRead (b : Choice)
    (_ : Choice.right ∈ (if b == .left then [b, .right] else [.right]))
    (_ : Unit) (bit : Bool) : Bool := bit
structure PropositionMember where
  proof : False ∈ propositionList
  bit : Bool
def propositionMemRead (_ : Unit) (bit : Bool) : PropositionMember :=
  ⟨.tail _ (.head _), bit⟩
end ListMetadataFixtures

namespace BoundarySubtypeFixtures
-- An external implementation cannot hide this statement-bearing proof field.
def payload (state : Bool) : {b : Bool // (137 : Nat) = 137} := ⟨state, rfl⟩
end BoundarySubtypeFixtures
