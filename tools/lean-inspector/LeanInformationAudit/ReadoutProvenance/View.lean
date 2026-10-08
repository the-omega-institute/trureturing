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
  protectedModules : Std.HashMap Name Bool
  constantsIdentity : USize
  isExporting : Bool := false

/-- Classify the compiler's dependency-first module inventory. Missing metadata
cannot justify an external leaf. -/
def compiledModuleClasses (modules : Array Name)
    (moduleData : Name → Option ModuleData) : Std.HashMap Name Bool := Id.run do
  let mut classes : Std.HashMap Name Bool := {}
  for name in modules do
    let inherited := match moduleData name with
      | none => true
      | some data => data.imports.any (fun item => classes[item.module]?.getD true)
    classes := classes.insert name
      (name.getRoot == `D5 || name.getRoot == `LeanInformationAudit || inherited)
  return classes

def CompiledView.fromArtifacts (store : RawArtifacts.Store) (mainModule : Name) : CompiledView := {
  find? := (store.constants[·]?)
  getProjectionFnInfo? := store.metadata.projections.find?
  isClass := store.metadata.classes.contains
  isInstance := store.metadata.instances.contains
  ownerOf := (store.owners[·]?)
  mainModule
  protectedModules := compiledModuleClasses store.moduleOrder store.modules.find?
  constantsIdentity := unsafe ptrAddrUnsafe store.constants }

end LeanInformationAudit.RegistrationGates
