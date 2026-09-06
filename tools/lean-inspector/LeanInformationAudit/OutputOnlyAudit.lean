import Lean

namespace LeanInformationAudit
open Lean

/-- Compiler-level dependency audit of the seal command and its helpers. Compiler internals
are trusted; inspector and application helpers are traversed, including private definitions.
Output producers may inspect presentation records, but no reachable helper may read files. -/
def auditSealOutputOnly (env : Environment) (entry root : Name) : Except String Unit := do
  let mut pending := #[(entry, false)]
  let mut visited : Std.HashSet (Name × Bool) := {}
  while !pending.isEmpty do
    let (name, output) := pending.back!
    pending := pending.pop
    if visited.contains (name, output) then continue
    visited := visited.insert (name, output)
    let visible := privateToUserName name
    let text := visible.toString
    let fileInput := (`IO.FS).isPrefixOf visible &&
      !#[``IO.FS.writeFile, ``IO.FS.createDirAll].contains visible
    let presentationInput := !output &&
      ((`LeanInformationAudit.KernelProjectionRecord).isPrefixOf visible ||
       (`LeanInformationAudit.ProjectionNode).isPrefixOf visible ||
       visible == ``Json.parse || text.startsWith "Lean.Json.getObjVal")
    if fileInput || presentationInput then
      throw s!"IE-C043 KernelProjectionUsedForAdmission consumer={privateToUserName entry} \
field={visible} root={root} catalog=system"
    -- These library effects implement elaboration, not artifact input. IO leaves above
    -- are checked before the library boundary, including file reads hidden in helpers.
    let owner := (env.getModuleIdxFor? name).map fun index =>
      env.allImportedModuleNames[index.toNat]!
    if owner.any (fun moduleName => (`Lean).isPrefixOf moduleName ||
        (`Init).isPrefixOf moduleName || (`Std).isPrefixOf moduleName) then
      continue
    let output := output || #[`LeanInformationAudit.prepareAnalysisProofs,
      `LeanInformationAudit.serializeV3Artifact, `LeanInformationAudit.serializeAsciiArtifact].contains visible
    if let some info := env.find? name then
      match info with
      | .defnInfo info =>
        pending := pending ++ info.value.getUsedConstants.map (·, output)
      | .opaqueInfo info =>
        pending := pending ++ info.value.getUsedConstants.map (·, output)
      | _ => pure ()

end LeanInformationAudit
