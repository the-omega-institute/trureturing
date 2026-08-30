/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/Core
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/Core
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical carriers for governance fixed-point obligations G-A through G-H. -/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- A gate holds when handwritten and derived statuses agree at every entry. -/
def Gate {Entry : Type u} {Status : Type v}
    (handwritten derived : Entry → Status) : Prop :=
  ∀ entry, handwritten entry = derived entry

/-- A blind deriver reads the context and entry, but no handwritten status. -/
abbrev BlindDeriver
    (Context : Type u) (Entry : Type v) (Status : Type w) :=
  Context → Entry → Status

/-- A self-reading deriver may inspect the complete handwritten status map. -/
abbrev SelfReadingDeriver
    (Context : Type u) (Entry : Type v) (Status : Type w) :=
  Context → (Entry → Status) → Entry → Status

/-- Regard a blind deriver as self-reading by ignoring the handwritten map. -/
def liftBlind
    {Context : Type u} {Entry : Type v} {Status : Type w}
    (d : BlindDeriver Context Entry Status) :
    SelfReadingDeriver Context Entry Status :=
  fun context _handwritten => d context

/-- A self-reading deriver is status-blind when it factors through `liftBlind`. -/
def StatusBlind
    {Context : Type u} {Entry : Type v} {Status : Type w}
    (D : SelfReadingDeriver Context Entry Status) : Prop :=
  ∃ d : BlindDeriver Context Entry Status, D = liftBlind d

/-- The canonical exchange of the two Boolean statuses. -/
def boolFlip : Bool → Bool
  | false => true
  | true => false

def PrefixExtension
    {Byte : Type u} (oldBytes newBytes : List Byte) : Prop :=
  ∃ suffix : List Byte, newBytes = oldBytes ++ suffix

def TailBytes
    {Byte : Type u} (document : List Byte) (start : Nat) :
    List Byte :=
  document.drop start

abbrev ContentKey (Byte : Type u) := List Byte

def contentKey
    {Byte : Type u} (bytes : List Byte) : ContentKey Byte :=
  bytes

inductive Verdict
  | pending
  | admit
  | reject
  deriving DecidableEq

abbrev Settlement (Id : Type u) := Id → Verdict

structure LedgerEntry (Id : Type u) (Byte : Type v) where
  logicalId : Id
  bytes : List Byte

def LedgerEntry.key
    {Id : Type u} {Byte : Type v}
    (entry : LedgerEntry Id Byte) : ContentKey Byte :=
  contentKey entry.bytes

abbrev ActiveIndex (Id : Type u) (Byte : Type v) :=
  Id → ContentKey Byte

def ActiveSource
    {Id : Type u} {Byte : Type v}
    (active : ActiveIndex Id Byte)
    (logicalId : Id) (key : ContentKey Byte) : Prop :=
  active logicalId = key

structure RekeyResult (Id : Type u) (Byte : Type v) where
  predecessor : ContentKey Byte
  newEntry : LedgerEntry Id Byte
  newActive : ActiveIndex Id Byte
  newSettlement : Settlement Id

def LegalTailRekey
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (result : RekeyResult Id Byte) : Prop :=
  tailEligible oldEntry.logicalId ∧
    PrefixExtension oldDocument newDocument ∧
    start ≤ oldDocument.length ∧
    oldEntry.bytes = TailBytes oldDocument start ∧
    ActiveSource active oldEntry.logicalId oldEntry.key ∧
    result.predecessor = oldEntry.key ∧
    result.newEntry.logicalId = oldEntry.logicalId ∧
    result.newEntry.bytes = TailBytes newDocument start ∧
    PrefixExtension oldEntry.bytes result.newEntry.bytes ∧
    result.newActive =
      Function.update active oldEntry.logicalId result.newEntry.key ∧
    result.newSettlement = settlement

def ConservativeRekey
    {Id : Type u} {Byte : Type v}
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (oldEntry : LedgerEntry Id Byte)
    (result : RekeyResult Id Byte) : Prop :=
  result.predecessor = oldEntry.key ∧
    result.newEntry.logicalId = oldEntry.logicalId ∧
    result.newSettlement = settlement ∧
    (∀ key,
      ActiveSource result.newActive oldEntry.logicalId key ↔
        key = result.newEntry.key) ∧
    ∀ logicalId,
      logicalId ≠ oldEntry.logicalId →
        result.newActive logicalId = active logicalId

def JointAllowed
    {Repair : Type u}
    (allow₁ allow₂ : Set Repair) : Set Repair :=
  allow₁ ∩ allow₂

def ReachableRepair
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair) : Prop :=
  ∃ repair,
    repair ∈ repairClass ∧
      repair ∈ JointAllowed allow₁ allow₂

def Deadlocked
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair) : Prop :=
  ¬ ReachableRepair repairClass allow₁ allow₂

def AllowedWithChannel
    {Repair : Type u}
    (allow₁ allow₂ channel : Set Repair) : Set Repair :=
  JointAllowed allow₁ allow₂ ∪ channel

def ConservativeChannel
    {Repair : Type u}
    (repairClass allow₁ allow₂ channel : Set Repair) : Prop :=
  JointAllowed allow₁ allow₂ ⊆
      AllowedWithChannel allow₁ allow₂ channel ∧
    AllowedWithChannel allow₁ allow₂ channel \
      JointAllowed allow₁ allow₂ = repairClass

end D5.S3.ConceptDynamics.GovernanceFixedPoint
