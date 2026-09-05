/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Arbitrary state spaces carry structural catalogs with canonical finite embeddings. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

/- Library-search audit trail (2026-09-05):
   * Repository searches for `StructuralArena`, `StructuralKernel`,
     `StructuralTheoremUnit`, and `StructuralCatalog` found no existing owner.
   * Exact current-tree hits `CIRPT.DecidableKernel.relation`,
     `CIRPT.DecidableKernel.equivalence`, `CIRPT.PrimitiveBundle.Index`, and
     `CIRPT.PrimitiveBundle.atom` are reused by the finite embedding.
   * Exact current-tree hits `InformationEscape.Arena`, `TheoremUnit`, and
     `Catalog` provide the finite carriers and stored `Fintype` instances.
   * Pinned Mathlib supplies `Equivalence` and `Fintype`; no existing
     arbitrary-state theorem-catalog structure with finite primitive bundles
     was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

/-- A structural arena has an arbitrary state carrier, with no finiteness or
decidable-equality requirement. -/
structure StructuralArena where
  State : Type u

/-- A possibly noncomputable equivalence kernel on a state carrier. -/
structure StructuralKernel (X : Type u) where
  relation : X -> X -> Prop
  equivalence : Equivalence relation

namespace StructuralKernel

/-- Forget a kernel's decision procedure while preserving its relation and
equivalence proof definitionally. -/
def ofDecidableKernel {X : Type u} (kernel : DecidableKernel X) :
    StructuralKernel X where
  relation := kernel.relation
  equivalence := kernel.equivalence

end StructuralKernel

/-- A proved statement equipped with a finite family of structural primitive
kernels on an arbitrary state carrier. -/
structure StructuralTheoremUnit (arena : StructuralArena.{u}) where
  PrimitiveIndex : Type v
  primitiveIndexFintype : Fintype PrimitiveIndex
  primitiveKernel : PrimitiveIndex -> StructuralKernel arena.State
  Statement : Prop
  proof : Statement

/-- A finite decidable catalog of structural theorem units. -/
structure StructuralCatalog (arena : StructuralArena.{u}) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index -> StructuralTheoremUnit.{u, v} arena

namespace Arena

/-- Forget the computational structure of a finite arena. -/
def toStructuralArena (arena : Arena.{u}) : StructuralArena.{u} where
  State := arena.State

end Arena

namespace TheoremUnit

/-- Embed a finite theorem unit by forgetting decidability from each primitive
kernel and retaining its proved statement. -/
def toStructuralTheoremUnit {arena : Arena.{u}}
    (unit : TheoremUnit.{u, v} arena) :
    StructuralTheoremUnit.{u, v} arena.toStructuralArena where
  PrimitiveIndex := unit.primitives.Index
  primitiveIndexFintype := unit.primitives.indexFintype
  primitiveKernel := fun index =>
    StructuralKernel.ofDecidableKernel (unit.primitives.atom index).kernel
  Statement := unit.Statement
  proof := unit.proof

end TheoremUnit

namespace Catalog

/-- Embed a finite catalog into the universal structural layer. -/
def toStructuralCatalog {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    StructuralCatalog.{u, v, w} arena.toStructuralArena where
  Index := catalog.Index
  indexFintype := catalog.indexFintype
  indexDecidableEq := catalog.indexDecidableEq
  theoremAt := fun index => (catalog.theoremAt index).toStructuralTheoremUnit

end Catalog

end D5.S3.ConceptDynamics.InformationEscape
