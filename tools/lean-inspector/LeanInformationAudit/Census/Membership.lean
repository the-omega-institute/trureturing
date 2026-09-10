import LeanInformationAudit.Census.Stream

namespace LeanInformationAudit.CensusStream

open Lean DispositionCensus

private def field (value : Json) (key : String) : IO Json := IO.ofExcept (value.getObjVal? key)
private def str (value : Json) (key : String) : IO String := IO.ofExcept (value.getObjValAs? String key)
private def arr (value : Json) (key : String) : IO (Array Json) := IO.ofExcept (value.getObjValAs? (Array Json) key)

private structure Candidate where
  moduleName : String
  key : String
  mode : String
  identity : String := ""
  name : String := ""

/-- A root stores module bits, sharing the graph's single name-to-index table.
No transitive string closure is retained per key. -/
private structure ModuleSet where
  indices : Std.HashMap String Nat
  bits : ByteArray

private def ModuleSet.contains (scope : ModuleSet) (name : String) : Bool :=
  (scope.indices[name]?).any (fun i => scope.bits[i]! != 0)

def resolveCollision (occurrences : Std.HashMap String Json) (identity : String) : Array String :=
  occurrences.toArray.filterMap fun (moduleName, record) =>
    if (record.getObjValAs? String "statement_id").toOption == some identity then
      some moduleName else none

def graphClosure (graph : Std.HashMap String (Array String)) (roots : Array String) :
    Except String (Array String) := do
  let mut visited : Std.HashSet String := {}
  let mut pending := roots.toList
  while !pending.isEmpty do
    let moduleName := pending.head!
    pending := pending.tail!
    if visited.contains moduleName then continue
    let some imports := graph[moduleName]?
      | throw s!"IE-C044 missing import header: {moduleName}"
    visited := visited.insert moduleName
    pending := imports.toList ++ pending
  return visited.toArray.qsort (· < ·)

def observation (owner : String) (name : Name) (id root : String)
    (error : Option String) : Json :=
  Json.mkObj [("theorem_name", nameJson name), ("statement_id", toJson id),
    ("class", toJson "observed"), ("payload", Json.mkObj [
      ("owning_module", nameJson owner.toName), ("root", nameJson root.toName),
      ("import_scope", Json.null), ("query_completed", toJson error.isNone),
      ("candidates", Json.arr #[]), ("note", toJson (error.getD
        "Exhaustive fresh olean query completed in the root scope; no supported evidence candidates."))])]

/-- Membership is a query over detached metadata. No Environment is imported.
Duplicate parts of one module are overrides, never distinct owners. -/
def membership (stream request destination : String) : IO Unit := do
  let input ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
  let keys ← IO.ofExcept <| input.getObjValAs? (Array (Array String)) "keys"
  let roots ← IO.ofExcept <| input.getObjValAs? (Array (String × Array String)) "roots"
  let assignment ← field input "assignment"
  let external ← IO.ofExcept <| input.getObjValAs? (Array (String × Array String)) "external_graph"
  let discoveryRoots ← IO.ofExcept <| input.getObjValAs? (Array String) "discovery_roots"
  let mut graph : Std.HashMap String (Array String) := Std.HashMap.ofArray external
  let mut owners : Std.HashMap String (Std.HashMap String Json) := {}
  let mut named : Std.HashMap String Json := {}
  let mut registrations : Std.HashMap String Json := {}
  let mut seals : Array (String × String) := #[]
  let mut modules : Std.HashSet String := {}
  let mut headers : Array Json := #[]
  let streamIn ← IO.FS.Handle.mk stream .read
  repeat
    let line ← streamIn.getLine
    if line.isEmpty then break
    let data ← IO.ofExcept <| Json.parse line
    let moduleName ← str data "module"
    modules := modules.insert moduleName
    let imports ← (← arr data "imports").mapM (fun entry => str entry "module")
    graph := graph.insert moduleName imports
    headers := headers.push <| Json.mkObj [("module", toJson moduleName),
      ("part", ← field data "part"), ("imports", ← field data "imports")]
    for owner in ← arr data "owners" do
      let name := (← field owner "name").compress
      owners := owners.insert name ((owners.getD name {}).insert moduleName owner)
    for entry in ← arr data "named" do
      let name := (← field entry "name").compress
      named := named.insert (moduleName ++ ":" ++ name) (entry.setObjVal! "module" (toJson moduleName))
    let registries ← field data "registries"
    for root in ← IO.ofExcept <| registries.getObjValAs? (Array String) "seals" do
      seals := seals.push (moduleName, root)
    for kind in ["finite", "structural"] do
      for entry in ← arr registries kind do
        registrations := registrations.insert entry.compress entry
  -- Every upstream header must stay outside the downstream evidence domain.
  -- Its package is imported by this project and cannot import the project back.
  for (moduleName, imports) in external do
    if modules.contains moduleName || imports.any modules.contains then
      throw <| IO.userError s!"IE-C044 upstream evidence boundary violated: {moduleName}"
  let discovery := Std.HashSet.ofArray (← IO.ofExcept <| graphClosure graph discoveryRoots)
  let mut evidence : Std.HashSet String := {}
  for (_, entry) in named do
    let moduleName ← str entry "module"
    if discovery.contains moduleName then evidence := evidence.insert moduleName
  for (_, entry) in registrations do
    let moduleName ← str entry "module"
    if discovery.contains moduleName then evidence := evidence.insert moduleName
  for (moduleName, root) in seals do
    if discovery.contains moduleName then evidence := evidence.insert root
  let evidenceModules := evidence.toArray.qsort (· < ·)
  let moduleNames := ((graph.toArray.map (·.1)) ++ roots.map (·.1)).qsort (· < ·)
  let moduleIndices := Std.HashMap.ofArray (moduleNames.mapIdx fun i name => (name, i))
  let mut scopes := #[]
  let mut scopeSets : Std.HashMap String ModuleSet := {}
  for (root, imports) in roots do
    let scope ← IO.ofExcept <| graphClosure graph (imports ++ evidenceModules)
    let indices := (scope.push root).map (moduleIndices.getD · 0) |>.qsort (· < ·)
    scopes := scopes.push (root, indices)
    let mut bits := ByteArray.mk (Array.replicate moduleNames.size (0 : UInt8))
    for i in indices do bits := bits.set! i 1
    scopeSets := scopeSets.insert root ⟨moduleIndices, bits⟩
  let rowsOut ← IO.FS.Handle.mk (destination ++ ".rows.jsonl") .write
  let mut candidates := #[]
  let mut errors := #[]
  let mut collisions := #[]
  let mut validationImports : Std.HashSet String := {}
  let allNamed := named.toArray.map (·.2) |>.qsort (fun a b => a.compress < b.compress)
  -- Decode the small index once, before the repository-sized key loop.
  let indexedNamed ← allNamed.mapM fun entry => do
    let mode ← str entry "mode"
    let identity ← if mode == "key" then str entry "identity" else pure ""
    let moduleName ← str entry "module"
    let key := (← field entry "key").compress
    let name := (← field entry "name").compress
    return ({ moduleName, key, mode, identity, name } : Candidate)
  let allRegistrations ← registrations.toArray.mapM fun (_, entry) => do
    let moduleName ← str entry "module"
    let key := (← field entry "key").compress
    return ({ moduleName, key, mode := "name" } : Candidate)
  for key in keys do
    unless key.size == 3 do throw <| IO.userError "IE-C044 invalid request triple"
    let owner := key[0]!
    let name ← IO.ofExcept <| parseNameKey key[1]!
    let id := key[2]!
    let root ← IO.ofExcept <| assignment.getObjValAs? String owner
    let some scope := scopeSets[root]? | throw <| IO.userError "IE-C044 missing root scope"
    let nameText := (nameJson name).compress
    let occurrences := owners.getD nameText {}
    let mut error : Option String := none
    if occurrences.size > 1 then
      let matching := resolveCollision occurrences id
      let resolved := matching.size == 1 && matching[0]! == owner
      collisions := collisions.push <| Json.mkObj [("key", toJson key),
        ("modules", toJson (occurrences.toArray.map (·.1) |>.qsort (· < ·))),
        ("matching_modules", toJson matching), ("resolved_by_statement", toJson resolved)]
      unless resolved do
        error := some s!"IE-C035 DuplicateAnalysisDisposition component=ownership_collision modules={toJson (occurrences.toArray.map (·.1) |>.qsort (· < ·))}"
    if error.isNone then
      if let some record := occurrences[owner]? then
        unless (← IO.ofExcept <| record.getObjValAs? Bool "matches") && scope.contains owner do
          error := some "IE-C036 DispositionIdentityMismatch component=owning_module_membership"
      else if occurrences.isEmpty then
        error := some "IE-C034 MissingAnalysisDisposition component=owning_module_membership"
      else
        error := some "IE-C036 DispositionIdentityMismatch component=owning_module_membership"
    let mut hits := #[]
    for entry in allRegistrations do
      if scope.contains entry.moduleName && entry.key == nameText then
        hits := hits.push entry
    for entry in indexedNamed do
      unless scope.contains entry.moduleName do continue
      let mode := entry.mode
      if mode == "support" then continue
      if mode == "unknown" then
        if error.isNone || error.get!.startsWith "IE-C034" then
          error := some s!"IE-C036 DispositionIdentityMismatch component=unclassifiable_named_key name={entry.name}"
      else if mode == "statement" ||
          (entry.key == nameText && (mode != "key" || entry.identity == id)) then
        -- Proposition equality requires isDefEq. Retain potential matches for
        -- assess; syntactic inequality is never used as a proof of absence.
        hits := hits.push entry
    if let some message := error then
      errors := errors.push <| Json.mkObj [("key", toJson key), ("error", toJson message)]
      rowsOut.putStrLn (observation owner name id root error).compress
    else if hits.isEmpty then
      rowsOut.putStrLn (observation owner name id root none).compress
    else
      candidates := candidates.push key
      validationImports := validationImports.insert owner
      -- All in-scope evidence, including support and seals, is provided by the
      -- discovery modules in this root's definition. Peer payloads are omitted.
      for entry in hits do validationImports := validationImports.insert entry.moduleName
  rowsOut.flush
  let result := Json.mkObj [("candidate_keys", toJson candidates),
    ("errors", Json.arr errors), ("scopes", toJson scopes), ("named", toJson allNamed),
    ("module_names", toJson moduleNames), ("collisions", Json.arr collisions),
    ("assignment", assignment), ("evidence_modules", toJson evidenceModules),
    ("validation_imports", toJson ((validationImports.toArray ++ evidenceModules).toList.eraseDups.toArray.qsort (· < ·))),
    ("headers", Json.arr headers), ("external_graph", toJson external)]
  IO.FS.writeFile destination (result.compress ++ "\n")

end LeanInformationAudit.CensusStream
