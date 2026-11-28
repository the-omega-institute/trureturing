import Lean
import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitPort.NativeQuot

open Lean

/-- Enumerate the public names of the strict basis for its standard namespace aliases. -/
def main (args : List String) : IO Unit := do
  let path :: referencePath :: modules := args | throw <| IO.userError "expected strict and official paths and module names"
  searchPathRef.set (System.SearchPath.parse path)
  let env ← importModules (modules.toArray.map fun module => {module := module.toName}) {} (level := .exported)
  let selected := modules.toArray.map String.toName
  searchPathRef.set (System.SearchPath.parse referencePath)
  let counterparts := selected.filterMap fun name =>
    if name == `OmegaMathlib then none else
      some ({module := name.replacePrefix name.getRoot (if name.getRoot == `OmegaInit then `Init else `Mathlib)} : Import)
  unsafe enableInitializersExecution
  let reference ← importModules counterparts {} (loadExts := true)
  let tokens := Parser.getTokenTable reference
  let identifier := fun (n : Name) => n.toStringWithToken (isToken := fun s => (tokens.find? s).isSome)
  let mut publicImports := #[]
  let mut rows := #[]
  let mut seals := #[]
  for owner in env.header.moduleNames, data in env.header.moduleData do
    unless selected.contains owner do continue
    publicImports := publicImports.push (owner.toString,
      (data.imports.filter (·.isExported)).map (·.module.toString))
    let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing module {owner}"
    let aliases := (aliasExtension.getModuleEntries env idx).filterMap fun (alias, _) =>
      if alias.getRoot == `Omega then some alias else none
    for name in data.constNames ++ aliases do
      if isPrivateName name || name.isInternal then continue
      if name.getRoot != `Omega then
        -- Kernel and compiler primitives keep their literal names. The Omega aliases of
        -- public primitives are enumerated separately from the same module's export table.
        if OmegaChecks.InitCompiler.RootNames.isPrimitive owner name ||
            OmegaChecks.InitPort.NativeQuot.isSupport owner name then continue
        throw <| IO.userError s!"unexpected public interface name {name} in {owner}"
      let .str parent leaf := name | throw <| IO.userError s!"unnamed export in {owner}"
      let original := parent.replacePrefix `Omega Name.anonymous
      let upstream := name.replacePrefix `Omega Name.anonymous
      if data.constNames.contains name && (env.find? name).any (fun info => info.isAxiom || info matches .opaqueInfo _) &&
          (reference.find? upstream).any (· matches .defnInfo _) then
        seals := seals.push (owner.toString, upstream.toString)
      -- Generated lemmas such as id.eq_1 can have a declaration as prefix
      -- without that prefix being an exportable namespace in its owning module.
      if (reference.find? original).any (fun info => !info.isInductive) || !reference.isNamespace original then
        rows := rows.push #[owner.toString, "Omega", "_root_", identifier upstream]
      else
        let namespaceName := if original.isAnonymous then "_root_" else identifier (`_root_ ++ original)
        rows := rows.push #[owner.toString, identifier parent, namespaceName, identifier (.str .anonymous leaf)]
  IO.println (Json.mkObj [("imports", toJson publicImports), ("names", toJson rows), ("seals", toJson seals)]).compress
