import LeanInformationAudit.RawArtifacts

namespace LeanInformationAudit.RegistrationGates
open Lean

/-- Immutable compiler facts used by provenance. The table identity is local
to one process and identifies syntax-cache inputs, never a report reuse key. -/
structure CompiledView where
  find? : Name → Option ConstantInfo
  getProjectionFnInfo? : Name → Option CompiledMetadata.Projection
  isClass : Name → Bool
  isInstance : Name → Bool
  ownerOf : Name → Option Name
  mainModule : Name
  protectedModules : Std.TreeMap Name Bool Name.quickCmp
  constantsIdentity : USize
  isExporting : Bool := false

def CompiledView.fromArtifacts (store : RawArtifacts.Store) (mainModule : Name) : CompiledView := {
  find? := (store.constants.find?)
  getProjectionFnInfo? := store.metadata.projections.find?
  isClass := store.metadata.classes.contains
  isInstance := store.metadata.instances.contains
  ownerOf := (store.owners.find?)
  mainModule
  protectedModules := store.protectedModules
  constantsIdentity := unsafe ptrAddrUnsafe store.constants }

end LeanInformationAudit.RegistrationGates
