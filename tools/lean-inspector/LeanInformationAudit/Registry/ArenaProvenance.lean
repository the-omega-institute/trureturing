import LeanInformationAudit.Registry.Repository

namespace LeanInformationAudit.ArenaProvenance
open Lean

def construction : Name := `LeanInformationAudit.arenaConstruction
def unsupported : Name := `LeanInformationAudit.arenaSourceUnsupported

/-- Resolve repository module addresses without reading source text. -/
def moduleSource (name : Name) : IO System.FilePath := do
  let path := name.toString.replace "." "/" ++ ".lean"
  if name.getRoot == `D5 || name.getRoot == `Reg then
    Repository.source path
  else if name.getRoot == `LeanInformationAudit then
    Repository.source ("tools/lean-inspector/" ++ path)
  else if name.getRoot == `LeanInformationAuditInterface then
    Repository.source ("tools/lean-inspector-interface/" ++ path)
  else findLean (← getSrcSearchPath) name

end LeanInformationAudit.ArenaProvenance
