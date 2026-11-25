import OmegaChecks.ModuleSurface
import OmegaChecks.ObjectOccurrences
import OmegaChecks.Interface

/-! Check the object references at their actual positions in each published Lean type. -/

open Lean

namespace OmegaChecks.ObjectOrigins

private def ownerOf (env : Environment) (n : Name) : IO Name := do
  let some i := env.getModuleIdxFor? n | throw <| IO.userError s!"missing compiled object {n}"
  return env.header.moduleNames[i]!

/-- All declarations, including private and compiler-generated ones, in a proof publication
must be proofs or direct references. Export aliases are recorded independently by Lean. -/
def proofReferences (env : Environment) (official : Bool) : IO (NameMap Name) := do
  let mut references := {}
  for mod in env.header.modules, data in env.header.moduleData do
    let owner := mod.module
    unless owner.getRoot == `OmegaMath do continue
    let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing proof module {owner}"
    for name in data.constNames do
      let some decl := env.find? name | throw <| IO.userError s!"missing proof declaration {name}"
      let reject := IO.userError s!"{owner}: {name} introduces a mathematical object; define it in D5 or use an admitted port"
      if decl.isUnsafe || decl.isAxiom then throw reject
      unless decl matches .thmInfo _ | .defnInfo _ | .opaqueInfo _ do throw reject
      let ctx : Core.Context := {fileName := "<proof publication>", fileMap := default}
      let state : Core.State := {env}
      if ← (Meta.isProp decl.type).run' |>.toIO' ctx state then
        let axioms ← (collectAxioms name : CoreM _).toIO' ctx state
        unless axioms.all (#[`Classical.choice, `Quot.sound, `propext].contains ·) do
          throw <| IO.userError s!"{owner}: unverified proof {name} depends on {axioms}"
        continue
      let .defnInfo d := decl | throw reject
      let .const target levels := d.value.consumeMData | throw reject
      unless levels == d.levelParams.map Level.param do throw reject
      references := references.insert name target
    for (alias, target) in aliasExtension.getModuleEntries env idx do
      references := references.insert alias target
  for (name, target) in references.toList do
    let owner ← ownerOf env target
    let allowed := if official then [`Init, `Mathlib, `D5, `OmegaMath] else [`OmegaInit, `OmegaMathlib, `D5, `OmegaMath]
    unless allowed.contains owner.getRoot do
      throw <| IO.userError s!"{name}: reference to {target} from unverified owner {owner}"
  return references

private structure FrozenObject where
  declaration_name_key : String
  kind : String
  deriving FromJson, BEq, Hashable

/-- Only D5 objects exposed by an OmegaMath public API require a canonical freeze here.
The repository's SL-008 check independently attests the current contents of each state. -/
private def checkPublishedFreezes (env : Environment) (references : NameMap Name) : IO Unit := do
  let mut visible : NameSet := {}
  for module in env.allImportedModuleNames do
    if module.getRoot == `OmegaMath then
      for dep in ← ModuleSurface.publicClosure env module do
        if dep.getRoot == `D5 || dep.getRoot == `OmegaMath then visible := visible.insert dep
  let mut objects : NameSet := {}
  for owner in visible do
    let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing publication module {owner}"
    for (alias, target) in aliasExtension.getModuleEntries env idx do
      unless isPrivateName alias do objects := objects.insert target
    for name in env.header.moduleData[idx]!.constNames do
      if isPrivateName name || name.isInternalOrNum || name.hasMacroScopes then continue
      let some decl := env.find? name | throw <| IO.userError s!"missing publication declaration {name}"
      objects := objects.insert name
      for dep in decl.type.getUsedConstants do objects := objects.insert dep
  let mut pending := objects.toList
  while let name :: rest := pending do
    pending := rest
    if let some target := references.find? name then
      unless objects.contains target do
        objects := objects.insert target
        pending := target :: pending
  let mut states : NameMap (Std.HashSet FrozenObject) := {}
  for name in objects do
    let owner ← ownerOf env name
    unless owner.getRoot == `D5 do continue
    let some decl := env.find? name | throw <| IO.userError s!"unknown published D5 object {name}"
    if decl.isTheorem || (← (Meta.isProp decl.type).run' |>.toIO' {fileName := "<publication>", fileMap := default} {env}) then continue
    let kind := match decl with
      | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quotient" | .thmInfo _ => "theorem"
    let path := modToFilePath "Golden/Frozen/state" owner "lean.json"
    if !states.contains owner then
      unless ← path.pathExists do throw <| IO.userError s!"OmegaMath publishes unfrozen D5 object {name} from {owner}: {path} is missing"
      let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      let rows : Array FrozenObject ← IO.ofExcept (json.getObjValAs? _ "declarations")
      states := states.insert owner (Std.HashSet.ofArray rows)
    unless (states.get! owner).contains ⟨Interface.frozenNameKey name, kind⟩ do
      throw <| IO.userError s!"OmegaMath publishes unfrozen D5 object {name} from {owner}: missing {kind} declaration key in {path}"

structure Result where
  /-- Supplied to the same semantic correspondence checker as public port declarations. -/
  bindings : NameMap Name := {}
  /-- A record for each occurrence in the published signature, including repeated uses. -/
  uses : Array Json := #[]

private def reserved : Name → Bool
  | .anonymous => false
  | .num pre _ => reserved pre
  | .str pre part => part == "OmegaMathlib" || reserved pre

/-- Detect declarations and aliases shadowing the standard qualifier even in privately
imported modules. Scoped namespaces and the mangling of private names do not confer ownership. -/
private def checkReserved (env : Environment) (official : Bool) : IO Unit := do
  for mod in env.header.modules, data in env.header.moduleData do
    let owner := mod.module
    let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing module {owner}"
    for n in data.constNames do
      if reserved (privateToUserName n).eraseMacroScopes then
        throw <| IO.userError s!"reserved standard declaration {n} belongs to {owner}"
    for (alias, target) in aliasExtension.getModuleEntries env idx do
      if reserved (privateToUserName alias).eraseMacroScopes then
        let upstream := alias.replacePrefix `OmegaMathlib .anonymous
        let expected := if official then upstream else `Omega ++ upstream
        let expectedOwner := if official then ModuleSurface.counterpart owner else owner
        unless owner.getRoot == `OmegaMathlib && alias.getRoot == `OmegaMathlib &&
            target == expected && (← ownerOf env target) == expectedOwner do
          throw <| IO.userError s!"reserved standard alias {alias} in {owner} targets {target}, expected an admitted port"

private def checkUse (strict publicStrict official : Environment) (decl pos lhs rhs : Name)
    (modules : NameSet) (registration : Bool) (s : Result) (report : Bool) : IO Result := do
  let src ← ownerOf strict lhs
  let dst ← ownerOf official rhs
  if ModuleSurface.isBasis src then
    let expected := lhs.replacePrefix `Omega .anonymous
    let owner := ModuleSurface.counterpart src
    unless lhs.getRoot == `Omega && publicStrict.contains lhs && !isPrivateName lhs &&
        expected == rhs && owner == dst do
      throw <| IO.userError s!"{decl} at {pos}: {lhs} in {src} requires {expected} in {owner}, found {rhs} in {dst}"
    let uses := if !report then s.uses else s.uses.push <| Json.mkObj [
      ("declaration", toJson decl.toString), ("position", toJson pos.toString),
      ("strictName", toJson lhs.toString), ("strictModule", toJson src.toString),
      ("upstreamName", toJson rhs.toString), ("upstreamModule", toJson dst.toString)]
    return { uses, bindings := s.bindings.insert lhs owner }
  if modules.contains src && !(src.getRoot == `D5 || src.getRoot == `OmegaMath) && !registration && !(strict.find? lhs).any (·.isTheorem) then
    throw <| IO.userError s!"{decl} at {pos}: mathematical object {lhs} in {src} requires a D5 owner or an admitted port"
  unless lhs == rhs && src == dst do
    throw <| IO.userError s!"{decl} at {pos}: {lhs} in {src} resolves to {rhs} in {dst}"
  return s

/-- A D5 definition can expose an object from a privately imported provider through its value.
Follow its kernel dependencies, including private helpers. Proof bodies do not define objects. -/
private def checkDefinitions (env : Environment) (project : NameSet) (roots : Array Name) : IO Unit := do
  let mut pending := roots.map (fun name => [name])
  let mut seen : NameSet := {}
  while let some path := pending.back? do
    pending := pending.pop
    let name := path.head!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throw <| IO.userError s!"missing project declaration {name}"
    let mut deps := info.type.getUsedConstants
    unless info.isTheorem do
      if let some body := info.value? (allowOpaque := true) then deps := deps ++ body.getUsedConstants
    for dep in deps do
      let owner ← ownerOf env dep
      if project.contains owner then
        let next := dep :: path
        unless owner.getRoot == `D5 || owner.getRoot == `OmegaMath || (env.find? dep).any (·.isTheorem) do
          let chain := String.intercalate " → " (next.reverse.map Name.toString)
          throw <| IO.userError s!"{chain}: mathematical object {dep} in {owner} requires a D5 owner or an admitted port"
        pending := pending.push next

/-- Compile-time identity at each use, in addition to kernel conversion of the full types.
The driver stages all project dependencies and supplies their modules independently of
which publication roots are selected. External dependencies are pinned by the workspace. -/
def check (strict publicStrict official : Environment) (modules roots : Array Name)
    (report : Bool) : IO Result := do
  let mut result : Result := {}
  if roots.isEmpty && !strict.allImportedModuleNames.any (·.getRoot == `OmegaMath) then return result
  checkReserved strict false
  checkReserved official true
  let project := NameSet.ofList modules.toList
  let refs ← proofReferences strict false
  let officialRefs ← proofReferences official true
  checkPublishedFreezes official officialRefs
  unless refs.size == officialRefs.size do throw <| IO.userError "proof publication references differ between backends"
  for (alias, target) in refs.toList do
    let some actual := officialRefs.find? alias | throw <| IO.userError s!"missing official proof publication reference {alias}"
    result := ← checkUse strict publicStrict official alias `reference target actual project false result report
  let mut visible : NameSet := {}
  let mut declarations := #[]
  for root in roots do
    unless project.contains root do throw <| IO.userError s!"unknown publication root {root}"
    for mod in ← ModuleSurface.publicClosure strict root do
      if project.contains mod then visible := visible.insert mod
  for owner in visible.toList.mergeSort Name.lt do
    let some i := strict.getModuleIdx? owner | throw <| IO.userError s!"missing strict module {owner}"
    let some j := official.getModuleIdx? owner | throw <| IO.userError s!"missing official module {owner}"
    -- Registration artifacts are compared by the frozen inventory and its typed inspector.
    let registration := owner.getRoot == `Reg || owner.getRoot == `LeanInformationAuditInterface
    let aliases := aliasExtension.getModuleEntries official j
    for (alias, target) in aliasExtension.getModuleEntries strict i do
      unless isPrivateName alias do
        let targetOwner ← ownerOf strict target
        let up := if ModuleSurface.isBasis targetOwner then target.replacePrefix `Omega .anonymous else target
        unless aliases.contains (alias, up) do throw <| IO.userError s!"{owner}: alias {alias} differs for {up}"
        result := ← checkUse strict publicStrict official alias `export target up project registration result report
        if !registration && project.contains targetOwner then declarations := declarations.push target
    for decl in strict.header.moduleData[i]!.constNames do
      if isPrivateName decl || decl.isInternalOrNum || decl.hasMacroScopes then continue
      let some a := strict.find? decl | throw <| IO.userError s!"missing strict declaration {decl}"
      let some b := official.find? decl | throw <| IO.userError s!"missing official declaration {decl}"
      result := ← checkUse strict publicStrict official decl `export decl decl project registration result report
      if !registration then declarations := declarations.push decl
      let left := occurrences a.type
      let right := occurrences b.type
      unless left.size == right.size do
        throw <| IO.userError s!"{decl}: different numbers of object occurrences ({left.size} vs {right.size})"
      for (pos, lhs) in left, (at_, rhs) in right do
        unless pos == at_ do throw <| IO.userError s!"{decl}: object {lhs} at {pos} moved to {at_} ({rhs})"
        result := ← checkUse strict publicStrict official decl pos lhs rhs project registration result report
  checkDefinitions strict project declarations
  return result

end OmegaChecks.ObjectOrigins
