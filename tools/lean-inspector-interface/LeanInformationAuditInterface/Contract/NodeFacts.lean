import LeanInformationAuditInterface.Contract.NodeFactsCore
import LeanInformationAuditInterface.Contract.Catalog
import LeanInformationAuditInterface.Contract.Registration

namespace LeanInformationAudit.Contract
open Lean
open D5.S3.ConceptDynamics.InformationEscape
universe u v w t s r o a

/-- The finite lift relates all realizations, not just the chosen actual one. -/
structure FiniteLiftFacts (finite : PrimitiveLawArena.{u,v,w})
    (family : DependentFamily.Arena.{t,s,r,o,a})
    (lift : PrimitiveRealization finite.signature → DependentFamily.Realization family.signature)
    (lower : DependentFamily.Realization family.signature → PrimitiveRealization finite.signature) where
  lowerLift : ∀ r, lower (lift r) = r
  liftLower : ∀ r, lift (lower r) = r
  law : ∀ r, family.Law (lift r) ↔ finite.Law r
  observations : List Name

structure AxisRow {T : Type u} (bundle : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{u,v} T) where
  index : bundle.Index
  axis : D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis
  correct : (bundle.atom index).axis = axis

structure AxisTable {T : Type u} (bundle : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{u,v} T) where
  rows : List (AxisRow bundle)
  nodup : (rows.map AxisRow.index).Nodup
  complete : ∀ i, i ∈ rows.map AxisRow.index

/-- Seal output is a typed literal view of its actual catalog. Functions occur
 only as indices and propositions; the report consumes constructor rows. -/
structure SealFactRow (catalog : SealCatalog.{u,v}) where
  position : Nat
  within : position < catalog.size
  row : SealRow (Catalog.ofVector catalog.units) ⟨position, within⟩
  correct : catalog.rows ⟨position, within⟩ = row
  bins : FiniteTable row.roleBins
  axes : AxisTable (catalog.units ⟨position, within⟩).primitives
  partition : FinitePartition catalog.arena.State
    (catalog.units ⟨position, within⟩).primitives.toKernel.relation
  stateOrder : partition.rows.map PartitionRow.item = catalog.enumeration.states

structure SealFacts (catalog : SealCatalog.{u,v}) where
  units : FiniteTable catalog.units
  rows : List (SealFactRow catalog)
  complete : rows.map SealFactRow.position = List.range catalog.size

end LeanInformationAudit.Contract
