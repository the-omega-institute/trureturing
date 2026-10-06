import LeanInformationAuditInterface.Contract.Core

namespace LeanInformationAudit.Contract
open Lean
universe u

/-- Coordinates address the unmodified compiler tree. A body edge enters one
 binder; a referenced declaration starts a separate coordinate. -/
inductive NodeEdge where
  | function | argument | domain | body | letType | letValue | letBody
  | metadata | projection
  deriving BEq, Inhabited, Repr

inductive NodePart where
  | type | value
  deriving BEq, Inhabited, Repr

structure NodeCoordinate where
  owner : Name
  declaration : Name
  part : NodePart
  path : List NodeEdge
  levels : List Level := []
  deriving BEq, Inhabited, Repr

/-- The report binds each operand to its coordinate by literal compiler-tree
 equality. The kernel checks the relation; its proof is never interpreted. -/
inductive NodeFact : Type (u + 1) where
  | data (T : Type u) (value : T) (location : NodeCoordinate)
  | type (T : Sort u) (location : NodeCoordinate)
  | proof (P : Prop) (value : P) (location : NodeCoordinate)
  | exact {T : Sort u} (left right : T) (leftAt rightAt : NodeCoordinate)
      (proof : ExactMatch left right)
  | equal {T : Sort u} (left right : T) (leftAt rightAt : NodeCoordinate)
      (proof : left = right)
  | equivalent (left right : Prop) (leftAt rightAt : NodeCoordinate)
      (proof : left ↔ right)

/-- A declared type boundary is a typed operand, not a guessed inference.
 `proof` boundaries retain the proposition while omitting the proof body. -/
structure NodeCoverage where
  roots : List NodeCoordinate
  facts : List Name

/-- A finite dependent function is published as literal rows. The report
 checks the positions are exactly 0,...,size-1; the kernel checks every value. -/
structure TableEntry {size : Nat} {T : Fin size → Type u} (value : ∀ i, T i) where
  position : Nat
  within : position < size
  item : T ⟨position, within⟩
  correct : value ⟨position, within⟩ = item

structure FiniteTable {size : Nat} {T : Fin size → Type u} (value : ∀ i, T i) where
  entries : List (TableEntry value)
  complete : entries.map TableEntry.position = List.range size

/-- Class labels certify a relation on a complete, duplicate-free enumeration.
 Canonical first-occurrence numbering is a mechanical report rule. -/
structure PartitionRow (T : Type u) where
  item : T
  classId : Nat

structure FinitePartition (T : Type u) (relation : T → T → Prop) where
  rows : List (PartitionRow T)
  nodup : (rows.map PartitionRow.item).Nodup
  complete : ∀ x, x ∈ rows.map PartitionRow.item
  classes : ∀ left ∈ rows, ∀ right ∈ rows,
    (left.classId = right.classId ↔ relation left.item right.item)

/-- Utility is a separate contract, with no four-slot escape obligation.
 Both indices must be the exact named compiler constants selected by SL-031. -/
structure UtilityRefutation (claim : Prop) (result : ¬ claim) where

/-- This excludes a fixed source proposition from the complete varying Law.
 It makes no claim that two true propositions are logically unequal. -/
structure StatementExclusion {T : Type u} (law : T → Prop) (statement : Prop) where
  lawLocation : NodeCoordinate
  statementLocation : NodeCoordinate
  excludes : ¬ ∀ x, law x ↔ statement

end LeanInformationAudit.Contract
