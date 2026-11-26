import OmegaChecks.ModuleSurface

/-! Snapshot public uses of mathematical constants with the compiler that built the publication. -/

open Lean

/-- Positions in the elaborated type survive aliases, notation and field resolution. -/
private def occurrences (e : Expr) : Array (Name × Name) :=
  collect e `type #[]
where
  collect (term : Expr) (pos : Name) (acc : Array (Name × Name)) : Array (Name × Name) :=
    match term with
    | .const n _ => acc.push (pos, n)
    | .proj s i target => collect target (.str pos "target") (acc.push (.num (.str pos "field") i, s))
    | .app fn arg => collect arg (.str pos "arg") (collect fn (.str pos "fn") acc)
    | .forallE _ dom body _ | .lam _ dom body _ =>
      collect body (.str pos "body") (collect dom (.str pos "binder") acc)
    | .letE _ type value body _ =>
      let acc := collect type (.str pos "letType") acc
      collect body (.str pos "body") (collect value (.str pos "value") acc)
    | .mdata _ body => collect body pos acc
    | _ => acc

/-- Traverse the observable expression with its binder context. A proof implementation
can be replaced by another proof of the same proposition without changing the object. -/
private partial def bodyOccurrences (term : Expr) (pos : Name := `value)
    (acc : Array (Name × Name) := #[]) : MetaM (Array (Name × Name)) := do
  if ← Meta.isProof term then return acc
  match term with
  | .const n _ => return acc.push (pos, n)
  | .proj s i target => bodyOccurrences target (.str pos "target") (acc.push (.num (.str pos "field") i, s))
  | .app fn arg => bodyOccurrences arg (.str pos "arg") (← bodyOccurrences fn (.str pos "fn") acc)
  | .forallE n dom body bi | .lam n dom body bi =>
    let acc ← bodyOccurrences dom (.str pos "binder") acc
    Meta.withLocalDecl n bi dom fun x => bodyOccurrences (body.instantiate1 x) (.str pos "body") acc
  | .letE n type value body _ =>
    let acc ← if ← Meta.isProp type then pure acc else do
      bodyOccurrences value (.str pos "value") (← bodyOccurrences type (.str pos "letType") acc)
    Meta.withLetDecl n type value fun x => bodyOccurrences (body.instantiate1 x) (.str pos "body") acc
  | .mdata _ body => bodyOccurrences body pos acc
  | _ => return acc

/-- Follow computational dependencies within the consumer. Imported official modules keep
their own publication boundary. Each helper is expanded once per published declaration. -/
private def publicationRefs (env : Environment) (mod : Name) (info : ConstantInfo)
    (moved : NameSet) (selectedBody : Bool) : MetaM (Array (Name × Name)) := do
  let owner? := fun n => (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx]!
  let localDep := fun n => owner? n == some mod || moved.contains n
  let pertinent := fun (e : Expr) => e.getUsedConstants.any fun n =>
    localDep n || (owner? n).any fun owner => owner.getRoot == `Mathlib
  let mut refs := occurrences info.type
  if let some full := env.find? info.name then
    if !full.isTheorem then
      if let some value := full.value? (allowOpaque := true) then
        if selectedBody || pertinent value then
          let pos := if info matches .defnInfo _ then `value else `implementation
          refs := refs ++ (← bodyOccurrences value pos)
  let mut seen : NameSet := ({} : NameSet).insert info.name
  let mut next := 0
  while next < refs.size do
    let (pos, name) := refs[next]!
    next := next + 1
    if !localDep name || seen.contains name then continue
    seen := seen.insert name
    let some helper := env.find? name | continue
    if helper.isTheorem then continue
    let some value := helper.value? (allowOpaque := true) | continue
    if ← Meta.isProof (mkConst name (helper.levelParams.map Level.param)) then continue
    let helperPos := Name.str pos "helper"
    if pertinent helper.type then
      refs := refs ++ (occurrences helper.type).map fun (p, n) => (helperPos ++ p, n)
    if pertinent value then
      refs := refs ++ (← bodyOccurrences value (.str helperPos "value"))
  return refs

private structure Request where
  path : String
  modules : Array String
  /-- On the candidate, measure the protected declarations, including references to local substitutes. -/
  selected : Option (Array String) := none
  selectedBodies : Option (Array String) := none
  protectedPath : Option String := none
  protectedModules : Array String := #[]
  checkPorts : Bool := false
  deriving FromJson

private def nameKey : Name → String
  | .anonymous => "n0"
  | .str parent s => s!"ns({nameKey parent},{s.utf8ByteSize}:{s})"
  | .num parent n => s!"nn({nameKey parent},{n})"

/-- Lean-generated universe binders can include the module name. Match them by
their argument position while retaining the entire kernel declaration. -/
private def sameMovedDefinition (before : DefinitionVal) (after : ConstantInfo) : Bool := Id.run do
  let .defnInfo candidate := after | return false
  if before.levelParams.length != candidate.levelParams.length then return false
  let rename := fun (e : Expr) =>
    e.instantiateLevelParams candidate.levelParams (before.levelParams.map Level.param)
  let aligned := { candidate with levelParams := before.levelParams,
                                  type := rename candidate.type, value := rename candidate.value }
  return ConstantInfo.defnInfo before == ConstantInfo.defnInfo aligned

/-- Load the view of an ordinary client of this one facade. Its imports determine
what it can see and which global reducibility attributes are active. -/
private def clientEnvironment (path : System.SearchPath) (mod : Name) (isModule : Bool) : IO Environment := do
  searchPathRef.set path
  let level := if isModule then OLeanLevel.exported else .private
  let mut client ← importModules #[{module := mod}] {} (level := level)
  for i in [:client.header.moduleNames.size] do
    for entry in reducibilityExtraExt.ext.getModuleEntries client i do
      if let .global value := entry then client := reducibilityExtraExt.addEntry client value
  return client.setExporting isModule

/-- A directly re-exported D5 definition may retain an old public spelling if its new
owner is independent of all Omega libraries and its compiled declaration is identical. -/
private def movedDeclarations (env : Environment) (omega : NameSet) (mod : Name)
    (current : ModuleData) (previousPath : String) : IO (Array ConstantInfo) := do
  let some path ← SearchPath.findWithExt (System.SearchPath.parse previousPath) "olean" mod
    | throw <| IO.userError s!"missing protected module {mod}"
  let (previous, _) ← readModuleData path
  let mut owners : NameMap ModuleData := {}
  let mut moved := #[]
  for before in previous.constants do
    let .defnInfo defn := before | continue
    if defn.safety != DefinitionSafety.safe || isPrivateName before.name || before.name.isInternalOrNum ||
        before.name.hasMacroScopes then continue
    let some idx := env.getModuleIdxFor? before.name | continue
    let owner := env.header.moduleNames[idx]!
    if owner == mod then continue
    -- Legacy files make ordinary imports available to their own importers.
    unless owner.getRoot == `D5 && !omega.contains owner && current.imports.any
        (fun dep => dep.module == owner && !dep.isMeta && (!current.isModule || dep.isExported)) do
      throw <| IO.userError s!"{mod} does not directly re-export {before.name} from a pure official D5 module ({owner})"
    unless owners.contains owner do
      let (publicData, _) ← readModuleData (← findOLean owner)
      owners := owners.insert owner publicData
    let some after := (owners.find? owner).bind (·.constants.find? (·.name == before.name))
      | throw <| IO.userError s!"moved definition {before.name} is not publicly exposed by {owner}"
    unless sameMovedDefinition defn after do throw <| IO.userError s!"moved definition {before.name} changed in {owner}"
    moved := moved.push after
  unless moved.isEmpty do
    let currentPath ← searchPathRef.get
    let lib ← getLibDir (← findSysroot)
    let oldClient ← clientEnvironment (System.SearchPath.parse previousPath ++ [lib]) mod previous.isModule
    let newClient ← clientEnvironment currentPath mod previous.isModule
    for info in moved do
      let some before := oldClient.find? info.name | throw <| IO.userError s!"missing public declaration {info.name}"
      let some after := newClient.find? info.name | throw <| IO.userError s!"moved definition {info.name} is hidden from {mod} clients"
      unless before.isDefinition && after.isDefinition &&
          (← OmegaChecks.ModuleSurface.keepsReduction oldClient newClient before after) do
        throw <| IO.userError s!"public unfolding changed for moved definition {info.name} in {mod}"
  return moved

def main (args : List String) : IO Unit := do
  let [request, output] := args | throw <| IO.userError "expected a standard identity request and result path"
  let input : Request ← IO.ofExcept <| Json.parse (← IO.FS.readFile request) >>= fromJson?
  searchPathRef.set (System.SearchPath.parse input.path ++ [← getLibDir (← findSysroot)])
  let imports := if input.checkPorts then input.modules.push "OmegaMathlib" else input.modules
  let env ← importModules (imports.map fun mod => {module := mod.toName, importAll := true}) {}
  let mut admitted : NameSet := {}
  if input.checkPorts then
    for owner in env.header.moduleNames, i in [:env.header.moduleNames.size] do
      unless owner.getRoot == `OmegaMathlib do continue
      for (alias, target) in aliasExtension.getModuleEntries env i do
        unless alias.getRoot == `OmegaMathlib do continue
        let some j := env.getModuleIdxFor? target | throw <| IO.userError s!"missing owner for {target}"
        let expected := alias.replacePrefix `OmegaMathlib .anonymous
        let expectedOwner := owner.replacePrefix `OmegaMathlib `Mathlib
        unless target == expected && env.header.moduleNames[j]! == expectedOwner do
          throw <| IO.userError s!"{alias} in {owner} exports {target} from {env.header.moduleNames[j]!}, expected {expected} from {expectedOwner}"
        admitted := admitted.insert target
  let selected := input.selected.map Std.HashSet.ofArray
  let selectedBodies := input.selectedBodies.map Std.HashSet.ofArray
  let mut omega : NameSet := {}
  if input.protectedPath.isSome then
    for owner in env.header.moduleNames, data in env.header.moduleData do
      if [`OmegaInit, `OmegaMathlib, `OmegaMath].contains owner.getRoot ||
          data.imports.any (fun dep => omega.contains dep.module) then omega := omega.insert owner
  let mut records := #[]
  for mod in input.modules do
    -- A module's .olean contains exactly its exported definitions. Legacy modules
    -- store their ordinary client-visible declarations in the same artifact.
    let (publicData, _) ← readModuleData (← findOLean mod.toName)
    let mut moved := #[]
    if let some path := input.protectedPath then
      if input.protectedModules.contains mod then
        moved ← movedDeclarations env omega mod.toName publicData path
    let movedNames := moved.foldl (init := ({} : NameSet)) fun names info => names.insert info.name
    for info in publicData.constants ++ moved do
      let name := info.name
      if isPrivateName name || name.isInternalOrNum || name.hasMacroScopes then continue
      let key := nameKey name
      let protectedDecl := selected.any (·.contains key)
      let refs ← (publicationRefs env mod.toName info movedNames (selectedBodies.any (·.contains key))).run' |>.toIO'
        {fileName := "<published declaration>", fileMap := default} {env}
      let mut uses := #[]
      for (pos, obj) in refs do
        let some j := env.getModuleIdxFor? obj | throw <| IO.userError s!"unknown compiled object {obj}"
        let owner := env.header.moduleNames[j]!
        unless protectedDecl || owner.getRoot == `Mathlib do continue
        uses := uses.push <| Json.mkObj [("position", toJson pos.toString), ("object", toJson obj.toString),
          ("objectKey", toJson (nameKey obj)), ("owner", toJson owner.toString),
          ("ported", toJson (admitted.contains obj))]
      unless uses.isEmpty do
        records := records.push <| Json.mkObj [("module", toJson mod), ("name", toJson name.toString),
          ("nameKey", toJson key), ("uses", Json.arr uses)]
  IO.FS.writeFile output (Json.arr records).compress
