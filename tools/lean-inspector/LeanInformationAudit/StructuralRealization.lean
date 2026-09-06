import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog

namespace LeanInformationAudit

open Lean
open D5.S3.ConceptDynamics.InformationEscape

universe u v w

/-- Typed structural readouts need neither finite states nor decidable outputs. -/
structure StructuralPrimitiveSignature where
  Index : Type v
  indexFintype : Fintype Index
  Output : Index → Type w

structure StructuralPrimitiveRealization (arena : StructuralArena.{u})
    (signature : StructuralPrimitiveSignature.{v, w}) where
  readout : ∀ i, arena.State → signature.Output i

structure StructuralPrimitiveLawArena (arena : StructuralArena.{u}) where
  signature : StructuralPrimitiveSignature.{v, w}
  Law : StructuralPrimitiveRealization arena signature → Prop

/-- A structural law must hold for one realization and fail for another. -/
def StructuralPrimitiveLawArena.Nondegenerate {arena : StructuralArena.{u}}
    (lawArena : StructuralPrimitiveLawArena.{u, v, w} arena) : Prop :=
  ∃ r₁ r₂ : StructuralPrimitiveRealization arena lawArena.signature,
    lawArena.Law r₁ ∧ ¬lawArena.Law r₂

def StructuralPrimitiveRealization.toTheoremUnit {arena : StructuralArena.{u}}
    {signature : StructuralPrimitiveSignature.{v, w}}
    (realization : StructuralPrimitiveRealization arena signature)
    (statement : Prop) (proof : statement) : StructuralTheoremUnit arena where
  PrimitiveIndex := signature.Index
  primitiveIndexFintype := signature.indexFintype
  primitiveKernel i := {
    relation := fun left right => realization.readout i left = realization.readout i right
    equivalence := eq_equivalence.comap (realization.readout i) }
  Statement := statement
  proof := proof

/-- The bridge and compiled kernels are checked against the registered unit. -/
structure StructuralLegacyPrimitiveRealization {arena : StructuralArena.{u}}
    (lawArena : StructuralPrimitiveLawArena.{u, v, w} arena) (statement : Prop)
    (realization : StructuralPrimitiveRealization arena lawArena.signature) : Prop where
  equivalence : statement ↔ lawArena.Law realization

/-- Closed numeric truth has no supplied object-level variation. The validator
also checks that both sides reduce to numerals and the theorem has this exact type. -/
structure ClosedNumericalObligation (theoremName : Name) (left right : Nat) : Prop where
  proof : left = right

/-- Failure to supply Fintype for this explicit primitive signature is witnessed
by Infinite. This records the boundary of this candidate family. -/
structure InfinitePrimitiveObligation (theoremName : Name) (arena : StructuralArena.{u})
    (Index : Type v) (Law : (Index → StructuralKernel arena.State) → Prop)
    (kernels : Index → StructuralKernel arena.State) (statement : Prop) : Prop where
  infinite : Infinite Index
  equivalence : statement ↔ Law kernels
  noFiniteSubfamily : ∀ selected : Finset Index, ∃ left right,
    (∀ i ∈ selected, (kernels i).relation left right) ∧
      ¬(∀ i, (kernels i).relation left right)

/-- A kernel proof that this proposed realization cannot supply the faithful bridge. -/
structure UnfaithfulPrimitiveObligation (theoremName : Name) {arena : StructuralArena.{u}}
    (lawArena : StructuralPrimitiveLawArena.{u, v, w} arena)
    (realization : StructuralPrimitiveRealization arena lawArena.signature)
    (statement : Prop) : Prop where
  no_bridge : ¬(statement ↔ lawArena.Law realization)

end LeanInformationAudit
