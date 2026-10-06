import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import LeanInformationAuditRegAnalysis.AnalysisDisposition

namespace LeanInformationAudit
open Lean D5.S3.ConceptDynamics.InformationEscape
universe u v w

/-- Catalog membership evidence for a generated structural theorem.
This type alone never grants structural provenance. -/
structure StructuralRegistrationEvidence (theoremName : Name) (arena : StructuralArena.{u})
    (unit : StructuralTheoremUnit.{u, v} arena)
    (catalogValue : StructuralCatalog.{u, v, w} arena) (index : catalogValue.Index)
    (statement : Prop) : Prop where
  membership : catalogValue.theoremAt index = unit
  statement_eq : unit.Statement = statement

/-- A computational classification for every structural catalog member. -/
structure StructuralCatalogSeal {arena : StructuralArena.{u}}
    (catalogValue : StructuralCatalog.{u, v, w} arena) where
  classification : ∀ i, Decidable (catalogValue.StructurallyLowersEscape i)

/-- A directionally explicit bounded comparison. The reverse direction is a
separate transfer obligation, checked only for the transferred constructor. -/
structure BoundedTruncationFamily (statement : Prop) where
  arena : Nat → Arena.{u}
  approximation : Nat → Prop
  restrict : ∀ bound, statement → approximation bound

/-- Named evidence for a certified closed unreachable reason, not an
`AnalysisObservation` or a general mathematical impossibility claim. Admission
requires a matching reason, a nonempty explanation, and `failedObligation = some
name` naming a kernel-checked, reason-specific obligation tied to the same theorem
and statement: `ClosedNumericalObligation`, `InfinitePrimitiveObligation`, or
`UnfaithfulPrimitiveObligation`, respectively. Reasons about a known carrier must
name it in `candidateArena`; the no-carrier reason requires `none`.
The census also checks absence of registered realizations in its import closure,
but registry absence alone cannot produce this evidence. -/
structure UnreachableElaborationEvidence (statement : Prop) where
  reason : UnreachableReason
  candidateArena : Option Name
  explanation : String
  failedObligation : Option Name := none


end LeanInformationAudit
