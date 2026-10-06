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


end LeanInformationAudit.Contract
