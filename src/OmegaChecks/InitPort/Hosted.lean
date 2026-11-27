import Lean
import OmegaChecks.InitCompiler.CompilerMarkers

/-! Share pinned physical roots with an ordinary Lean importer. -/

open Lean

private def parts (path : System.FilePath) := #[path, path.addExtension "server", path.addExtension "private"]

private def sameImplementation (ported pinned : ConstantInfo) : Bool := Id.run do
  unless ported.name == pinned.name && ported.levelParams == pinned.levelParams &&
      ported.type.equal pinned.type do return false
  if OmegaChecks.InitPort.CompilerMarkers.valid ported then
    return pinned.isAxiom && pinned.isUnsafe
  if let .thmInfo _ := ported then return pinned matches .thmInfo _
  unless ported == pinned do return false
  unless (ported.value? (allowOpaque := true)).map ExprStructEq.mk ==
      (pinned.value? (allowOpaque := true)).map ExprStructEq.mk do return false
  if let .recInfo a := ported then
    let .recInfo b := pinned | return false
    return (a.rules.zip b.rules).all (fun (x, y) => x.rhs.equal y.rhs)
  return true

private def physicalRoot (name : Name) : Bool :=
  name.getRoot != `Omega && !(`_private.OmegaInit).isPrefixOf name

private def project (source output std : System.FilePath) (owner : Name) : IO Unit := do
  let raw := modToFilePath source owner "olean"
  let path := modToFilePath output owner "olean"
  let strict := (← readModuleDataParts (parts raw)).map Prod.fst
  let candidates := strict[2]!.constants.filter fun ci => physicalRoot ci.name
  if candidates.isEmpty then return
  let original := owner.replacePrefix `OmegaInit `Init
  let pinned := (← readModuleDataParts (parts (modToFilePath std original "olean"))).map Prod.fst
  let byName := pinned[2]!.constants.foldl (init := ({} : NameMap ConstantInfo)) fun m ci => m.insert ci.name ci
  let mut shared : NameSet := {}
  for ci in candidates do
    if let some target := byName.find? ci.name then
      unless sameImplementation ci target do throw <| IO.userError s!"incompatible physical root {owner}/{ci.name}"
      shared := shared.insert ci.name
  if shared.isEmpty then return
  IO.FS.createDirAll path.parent.get!
  let mut outputParts := #[]
  for data in strict, file in parts path do
    let constants := data.constants.filter fun ci => !shared.contains ci.name
    let result := { data with
      constants
      constNames := constants.map (·.name)
      extraConstNames := data.extraConstNames.filter (!shared.contains ·)
      imports := data.imports.push {module := original} }
    outputParts := outputParts.push (file, result)
  saveModuleDataParts owner outputParts

def main (args : List String) : IO Unit := do
  let source :: output :: owners := args | throw <| IO.userError "expected a strict library, output directory and module names"
  let std ← getLibDir (← findSysroot)
  for owner in owners do
    let name := owner.toName
    unless name.getRoot == `OmegaInit do throw <| IO.userError s!"expected an OmegaInit module, got {name}"
    project source output std name
