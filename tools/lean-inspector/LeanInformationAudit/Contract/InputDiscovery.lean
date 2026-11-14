import LeanInformationAudit.Contract.SourceAudit

open Lean

/-- Detach the compiler input fact before releasing mapped olean regions. -/
@[noinline] private unsafe def emitInputProjection (moduleName : String)
    (paths : Array String) (destination : String) : IO (Array CompactedRegion × Nat) := do
  let parts ← readModuleDataParts (paths.map System.FilePath.mk)
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for (data, _) in parts do
    for info in data.constants do constants := constants.insert info.name info
  let mut inputs := #[]
  for (name, info) in constants.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let head := info.type.getAppFn.constName?.getD .anonymous
    unless LeanInformationAudit.Contract.SourceAudit.isInput info do continue
    discard <| IO.ofExcept (LeanInformationAudit.Contract.SourceAudit.checkInputDefinition info)
    if head == `LeanInformationAudit.Contract.ExpectedDeclaration then
      throw <| IO.userError s!"contract.root_structure:independent_expected_not_allowed:{moduleName}:{name}"
    inputs := inputs.push (Json.mkObj [("type", toJson head.toString),
      ("owner", toJson moduleName), ("name", toJson name.toString)])
  IO.FS.writeFile destination ((Json.mkObj [
    ("schema", toJson "stratalint-judge-input-projection-v1"),
    ("module", toJson moduleName), ("inputs", Json.arr inputs)]).compress ++ "\n")
  return (parts.map (·.2), inputs.size)

unsafe def main (args : List String) : IO UInt32 := do
  try
    let [moduleName, olean, destination] := args
      | throw <| IO.userError "expected module, own olean and destination"
    let mut paths := #[]
    for suffix in #["", ".server", ".private"] do
      let path := olean ++ suffix
      if ← (System.FilePath.mk path).pathExists then paths := paths.push path
    unless paths[0]? == some olean do
      throw <| IO.userError s!"contract.discovery:missing_olean:{moduleName}"
    let (regions, count) ← emitInputProjection moduleName paths destination
    for region in regions.reverse do region.free
    IO.println s!"LEAN_INSPECTOR_DISCOVER module={moduleName} inputs={count}"
    if let some path ← IO.getEnv "STRATALINT_INSPECTOR_MODULE_WORK" then
      IO.FS.withFile path .append fun out => out.putStr <| (Json.mkObj [
      ("operation", toJson "discover"), ("module", toJson moduleName)]).compress ++ "\n"
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"input-discovery: {error}"
    return 1
