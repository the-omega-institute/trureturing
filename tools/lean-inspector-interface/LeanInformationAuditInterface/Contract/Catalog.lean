import LeanInformationAuditInterface.Contract.Implementation
import D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog

namespace LeanInformationAudit.Contract
open Lean
open D5.S3.ConceptDynamics.InformationEscape
universe u v

structure TypeRef where
  name : Name
  type : Type u

structure TemplateEnrollment {T : Sort u} (template : T) where
  name : Name
  version : Nat
  constructors : Array (TypeRef.{v})
  options : Array OptionSetting

/-- Expectations are independent of discovered registrations. -/
structure ExpectedOccurrence where
  statement : Prop
  proof : statement
  theoremName : Name
  objectArenaName : Name
  statementIdentity : Option String
  registrationModuleName : Name

structure RootCatalogData where
  rootId : Name
  expected : Array ExpectedOccurrence
  source : Array ExpectedOccurrence
  baseline : Array ExpectedOccurrence
  companionPrefix : Option Name

structure RootCatalog where
  data : RootCatalogData

structure ExpectedDeclaration where
  rootId : Name
  occurrence : ExpectedOccurrence

/-- Each zero row carries its closure membership; every positive row carries
its exact lowering proposition. Both constructors are indexed by the count. -/
inductive SealRowConclusion {arena : Arena.{u}} (catalog : Catalog.{u,v,0} arena)
    (index : catalog.Index) (unique : Nat) : Type where
  | positive (countPositive : 0 < unique) (proof : Catalog.LowersEscape catalog index)
  | zero (countZero : unique = 0) (proof : Catalog.TrivialInCatalog catalog index)
      (closure : (catalog.theoremAt index).primitives.toKernel ∈ catalog.semanticClosureWithout index)

structure SealRow {arena : Arena.{u}} (catalog : Catalog.{u,v,0} arena)
    (index : catalog.Index) where
  unique : Nat
  uniqueEq : catalog.uniqueCaptureCount index = unique
  without : Nat
  withoutEq : catalog.escapeNumerator (catalog.without index) = without
  roleBins : Fin 15 → Nat
  roleEq : ∀ bucket, catalog.roleHistogram index (Catalog.roleSignatureOfBucket bucket) = roleBins bucket
  roleTotal : Finset.sum Finset.univ roleBins = unique
  conclusion : SealRowConclusion catalog index unique

inductive SealCatalogConclusion {arena : Arena.{u}} (catalog : Catalog.{u,v,0} arena) : Type where
  | redundant (proof : Catalog.CatalogRedundant catalog)
  | irredundant (proof : CatalogIrredundant catalog)

/-- Counts, classifications and collisions concern the same vector catalog.
The judge reconstructs its membership and ordering from raw registrations. -/
structure SealCatalog where
  arenaName : Name
  catalogId : Name
  arena : Arena.{u}
  size : Nat
  units : Fin size → TheoremUnit.{u,v} arena
  nondegenerate : arena.Nondegenerate
  bundleNonempty : ∀ index, (units index).primitives.Nonempty
  stateCard : Nat
  stateCardEq : arena.card = stateCard
  full : Nat
  fullEq : (Catalog.ofVector units).escapeNumerator (Catalog.ofVector units).fullIndexSet = full
  rows : ∀ index : Fin size, SealRow (Catalog.ofVector units) index
  collisions : Array (Sigma fun left : Fin size => Sigma fun right : Fin size =>
    Subtype (fun _ : left ≠ right => Catalog.KernelEquivalent (Catalog.ofVector units) left right))
  conclusion : SealCatalogConclusion (Catalog.ofVector units)
  enumeration : arena.StateEnumeration

structure Seal where
  rootId : Name
  catalogs : Array (SealCatalog.{u,v})
  options : Array OptionSetting

end LeanInformationAudit.Contract
