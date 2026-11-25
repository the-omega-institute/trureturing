import OmegaChecks.ObjectOccurrences

/-! Snapshot public uses of mathematical constants with the compiler that built the publication. -/

open Lean

private structure Request where
  path : String
  modules : Array String
  /-- On the candidate, measure the protected declarations, including references to local substitutes. -/
  selected : Option (Array String) := none
  deriving FromJson

private def nameKey : Name → String
  | .anonymous => "n0"
  | .str parent s => s!"ns({nameKey parent},{s.utf8ByteSize}:{s})"
  | .num parent n => s!"nn({nameKey parent},{n})"

def main (args : List String) : IO Unit := do
  let [request, output] := args | throw <| IO.userError "expected a standard identity request and result path"
  let input : Request ← IO.ofExcept <| Json.parse (← IO.FS.readFile request) >>= fromJson?
  searchPathRef.set (System.SearchPath.parse input.path ++ [← getLibDir (← findSysroot)])
  let env ← importModules (input.modules.map fun mod => {module := mod.toName}) {}
  let selected := input.selected.map Std.HashSet.ofArray
  let mut records := #[]
  for mod in input.modules do
    let some i := env.getModuleIdx? mod.toName | throw <| IO.userError s!"missing selected module {mod}"
    for name in env.header.moduleData[i]!.constNames do
      if isPrivateName name || name.isInternalOrNum || name.hasMacroScopes then continue
      let key := nameKey name
      if selected.any (!·.contains key) then continue
      let some info := env.find? name | throw <| IO.userError s!"missing compiled declaration {name}"
      let mut uses := #[]
      for (pos, obj) in OmegaChecks.ObjectOrigins.occurrences info.type false do
        let some j := env.getModuleIdxFor? obj | throw <| IO.userError s!"unknown compiled object {obj}"
        let owner := env.header.moduleNames[j]!
        if selected.isNone && owner.getRoot != `Mathlib then continue
        uses := uses.push <| Json.mkObj [("position", toJson pos.toString), ("object", toJson obj.toString),
          ("objectKey", toJson (nameKey obj)), ("owner", toJson owner.toString)]
      unless uses.isEmpty do
        records := records.push <| Json.mkObj [("module", toJson mod), ("name", toJson name.toString),
          ("nameKey", toJson key), ("uses", Json.arr uses)]
  IO.FS.writeFile output (Json.arr records).compress
