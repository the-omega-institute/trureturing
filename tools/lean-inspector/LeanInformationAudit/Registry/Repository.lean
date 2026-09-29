import Lean

namespace LeanInformationAudit.Repository

/-- Judge implementation and its stable Interface, by compiler module owner.
Declaration namespaces do not identify the package that supplied a definition. -/
def isInspectorModule (name : Lean.Name) : Bool :=
  (`LeanInformationAudit).isPrefixOf name || (`LeanInformationAuditInterface).isPrefixOf name

/-- Local data/type bodies include registration support; external libraries remain
opaque. This classifies a supplied owner, without enumerating loaded modules. -/
def isModule (name : Lean.Name) : Bool :=
  isInspectorModule name || (`D5).isPrefixOf name || (`Reg).isPrefixOf name || name == `Trureturing

/-- Resolve the current checkout at runtime, including from a nested Lake package.
Only logical relative source names are stored in evidence; no build-host path is
captured in an olean. The root Lake configuration and toolchain identify the root. -/
partial def rootFrom (directory : System.FilePath) : IO System.FilePath := do
  if (← (directory / "lakefile.toml").pathExists) &&
      (← (directory / "lean-toolchain").pathExists) then
    return ← IO.FS.realPath directory
  if let some parent := directory.parent then
    if parent != directory then return ← rootFrom parent
  throw <| IO.userError "repository root not found (lakefile.toml, lean-toolchain)"

def root : IO System.FilePath := do rootFrom (← IO.currentDir)

def source (path : String) : IO System.FilePath := do
  return (← root) / path

end LeanInformationAudit.Repository
