import Lean

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
    unless before == after do throw <| IO.userError s!"moved definition {before.name} changed in {owner}"
    moved := moved.push after
  return moved

def main (args : List String) : IO Unit := do
  let [request, output] := args | throw <| IO.userError "expected a standard identity request and result path"
  let input : Request ← IO.ofExcept <| Json.parse (← IO.FS.readFile request) >>= fromJson?
  searchPathRef.set (System.SearchPath.parse input.path ++ [← getLibDir (← findSysroot)])
  let imports := if input.checkPorts then input.modules.push "OmegaMathlib" else input.modules
  let env ← importModules (imports.map fun mod => {module := mod.toName}) {}
  let mut admitted : NameSet := {}
  if input.checkPorts then
    for owner in env.header.moduleNames, i in [:env.header.moduleNames.size] do
      unless owner.getRoot == `OmegaMathlib do continue
      for (alias, target) in aliasExtension.getModuleEntries env i do
        unless alias.getRoot == `OmegaMathlib do continue
        let some j := env.getModuleIdxFor? target | throw <| IO.userError s!"missing owner for {target}"
        if target == alias.replacePrefix `OmegaMathlib .anonymous &&
            env.header.moduleNames[j]! == owner.replacePrefix `OmegaMathlib `Mathlib then
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
    let mut declarations := publicData.constants
    if let some path := input.protectedPath then
      if input.protectedModules.contains mod then
        declarations := declarations ++ (← movedDeclarations env omega mod.toName publicData path)
    for info in declarations do
      let name := info.name
      if isPrivateName name || name.isInternalOrNum || name.hasMacroScopes then continue
      let key := nameKey name
      let protectedDecl := selected.any (·.contains key)
      let mut refs := occurrences info.type
      let value? := (env.find? name).bind fun decl =>
        if decl.isTheorem then none else decl.value? (allowOpaque := true)
      if let some value := value? then
        let relevant := selectedBodies.any (·.contains key) || (value.getUsedConstants.any fun n =>
          (env.getModuleIdxFor? n).any fun idx => env.header.moduleNames[idx]!.getRoot == `Mathlib)
        if relevant then
          let pos := if info matches .defnInfo _ then `value else `implementation
          let positions ← (bodyOccurrences value pos).run' |>.toIO'
            {fileName := "<published definition>", fileMap := default} {env}
          refs := refs ++ positions
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
