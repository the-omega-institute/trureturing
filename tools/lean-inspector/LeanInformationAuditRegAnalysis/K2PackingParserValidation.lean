import Reg.Support.CompiledNodeTerm

open Lean Elab Command

namespace K2PackingParserValidation

private def inputManifestSha256 : String := "33706a604ee0cefb7e65d76e147378ba1bcdd6bbbb5d0a55df11672bdec2e611"

private partial def eraseSourceInfo : Syntax → Syntax
  | .missing => .missing
  | .node _ kind args => .node .none kind (args.map eraseSourceInfo)
  | .atom _ value => .atom .none value
  | .ident _ rawValue value preresolved => .ident .none rawValue value preresolved

private def parse (env : Environment) (category : Name) (source : String) :
    CommandElabM Syntax := do
  match Parser.runParserCategory env category source with
  | .ok parsedSyntax => return eraseSourceInfo parsedSyntax
  | .error message => throwError "packing.parse:{category}:{message}"

def check : CommandElabM Unit := do
  let env ← getEnv
  let directory : System.FilePath :=
    "/Users/auricstudio/.ie0904/reg-iface-split-1001/p3-k2"
  let source ← liftIO <| IO.FS.readFile (directory / "packing-parser-pairs.jsonl")
  let mut results : Array Json := #[]
  let mut termCount : Nat := 0
  let mut commandCount : Nat := 0
  for line in source.splitOn "\n" do
    if line.isEmpty then continue
    let row ← liftIO <| IO.ofExcept <| Json.parse line
    let identity ← liftIO <| IO.ofExcept <| row.getObjValAs? String "id"
    let category ← liftIO <| IO.ofExcept <| row.getObjValAs? String "category"
    let original ← liftIO <| IO.ofExcept <| row.getObjValAs? String "original"
    let packed ← liftIO <| IO.ofExcept <| row.getObjValAs? String "packed"
    let before ← parse env category.toName original
    let after ← parse env category.toName packed
    unless before.eqWithInfo after do
      throwError "packing.syntax_tree_changed:{identity}:{category}"
    if category == "term" then termCount := termCount + 1
    if category == "command" then commandCount := commandCount + 1
    results := results.push <| Json.mkObj [
      ("id", toJson identity), ("category", toJson category), ("equal", toJson true)]
  let negativeBefore ← parse env `term "fun (x : Nat) => let y := x; y"
  let negativeAfter ← parse env `term "fun (x : Nat) => let y := x; x"
  if negativeBefore.eqWithInfo negativeAfter then
    throwError "packing.parser_negative_guard_ineffective"
  let result := Json.mkObj [
    ("scope", toJson "Pinned Lean parser AST comparison after recursively erasing SourceInfo"),
    ("input_sha256", toJson inputManifestSha256),
    ("pairs", toJson results.size), ("terms", toJson termCount),
    ("commands", toJson commandCount), ("negative_guard", toJson true),
    ("issues", Json.arr #[]), ("results", Json.arr results)]
  let destination := directory / "packing-parser-validation.json"
  let temporary := directory / "packing-parser-validation.json.tmp"
  liftIO <| IO.FS.writeFile temporary (result.pretty ++ "\n")
  liftIO <| IO.FS.rename temporary destination
  logInfo m!"packing.parser: {results.size} pairs, {termCount} terms, {commandCount} commands"

end K2PackingParserValidation

run_cmd K2PackingParserValidation.check
