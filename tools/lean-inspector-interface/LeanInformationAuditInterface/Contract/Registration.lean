import LeanInformationAuditInterface.Contract.Implementation

namespace LeanInformationAudit.Contract
open Lean
open D5.S3.ConceptDynamics.InformationEscape
universe d h i u v w t s r o a k

/-- Raw operands accompany arena-indexed, kernel-checked mathematical obligations.
Enrollment, provenance and source reconstruction remain structural judge work. -/
structure Registration {P : Prop} (target : P)
    (Readout : Type d) (From : Type h) (Residual : Sort i) where
  unitName : Name
  realizationName : Name
  realizationSource : Option Name
  generated : Bool
  arena : ArenaRef.{u,v,w,t,s,r,o,a,k}
  objectArena : ArenaRef.{u,v,w,t,s,r,o,a,k}
  catalog : Name
  localNames : Bool
  realization : Implementation.{u,v,w,t,s,r,o,a,k} P
  correspondence : Implementation.Correspondence realization arena objectArena
  bundleNonempty : Obligation realization.BundleNonempty
  readout : Option Readout
  variation : realization.VariationEvidence
  sensitivity : Obligation realization.Sensitivity
  partialSensitivity : Option (Implementation.PartialSlotEvidence realization)
  escapeFrom : Option From
  sourceSelection : Option SourceSelection
  continuation : Continuation Residual
  familyRecord : Option (Sigma fun family : DependentFamily.Arena.{t,s,r,o,a} => Ref (DependentFamily.Registration family P))
  options : Array OptionSetting

end LeanInformationAudit.Contract
