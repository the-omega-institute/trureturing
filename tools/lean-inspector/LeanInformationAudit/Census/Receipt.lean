import LeanInformationAudit.Census.Query


namespace LeanInformationAudit.CensusReceipt

open Lean Meta DispositionCensus

/-- Hash the exact bytes already read, through stdin, without reopening a path.
Report hashing is run-local IO; the pure SHA implementation remains available
to the certificate layer. Interpreting its rounds over a full export dominated
the candidate pass, while the native digest preserves the same byte binding. -/
def hashReportBytes (bytes : String) : IO String := do
  let digestProcess ← IO.Process.output { cmd := "python3", args := #["-c",
    "import hashlib,sys;print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())"] } (some bytes)
  let hash := digestProcess.stdout.trimAscii.toString
  unless digestProcess.exitCode == 0 && hash.length == 64 &&
      hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError "IE-C044 native report digest failed"
  return "sha256:" ++ hash

def readRequest (path : String) : MetaM (Json × FrozenReport) := do
  let input ← ofExcept <| Json.parse (← IO.FS.readFile path)
  let object ← ofExcept <| input.getObj?
  unless object.size == 4 && ["head", "keys", "report", "report_sha256"].all object.contains do
    throwError "census query: input requires exactly head, keys, report and report_sha256"
  let head ← ofExcept <| stringField input "head"
  let bytes ← IO.FS.readFile (← ofExcept <| stringField input "report")
  let json ← ofExcept <| Json.parse bytes
  let report ← ofExcept <| parseReportJson json (← hashReportBytes bytes)
  ofExcept <| checkReportBinding head (← ofExcept <| stringField input "report_sha256") report
  let mut owners : Std.HashMap String (String × Name) := {}
  for node in ← ofExcept <| json.getObjValAs? (Array Json) "nodes" do
    let path ← ofExcept <| stringField node "repo_path"
    if head == "fixture-head" && !path.startsWith "LeanInformationAudit/Tests/" then
      throwError "query receipt: synthetic fixture cannot query production paths"
    if (← ofExcept <| stringField node "freeze_status") != "frozen" then continue
    let owner := String.intercalate "." ((path.dropEnd 5).toString.splitOn "/")
    for decl in ← ofExcept <| node.getObjValAs? (Array Json) "declarations" do
      if (← ofExcept <| stringField decl "kind") != "theorem" then continue
      let name ← ofExcept <| parseNameKey (← ofExcept <| stringField decl "declaration_name_key")
      owners := owners.insert (← ofExcept <| stringField decl "statement_id") (owner, name)
  if head != "fixture-head" then
    let actual ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    unless actual.exitCode == 0 && actual.stdout.trimAscii.toString == head do
      throwError "query receipt: report revision differs from environment HEAD"
    let pinned ← IO.Process.output { cmd := "git", args := #["diff", "--exit-code", "HEAD", "--",
      "D5", "lean-toolchain", "lake-manifest.json", "lakefile.toml", "Golden/Frozen/state"] }
    unless pinned.exitCode == 0 do throwError "query receipt: production inputs are not pinned"
  for key in ← ofExcept <| input.getObjValAs? (Array (Array String)) "keys" do
    unless key.size == 3 do throwError "query receipt: expected module/name/identity triple"
    let name ← ofExcept <| parseNameKey key[1]!
    unless owners[key[2]!]? == some (key[0]!, name) do
      throwError "query receipt: requested key is not in the immutable report"
  return (input, report)

/-- Candidate output is run-local. The whole-stream receipt binds these bytes,
all tracked olean parts, graph, root scopes, and query source bundle. -/
def write (destination : String) (result : Json) : IO Unit := do
  let bytes := result.compress ++ "\n"
  let receipt := Json.mkObj [
    ("head", ← IO.ofExcept <| result.getObjVal? "head"),
    ("report_sha256", ← IO.ofExcept <| result.getObjVal? "report_sha256"),
    ("rows_sha256", toJson ("sha256:" ++ Sha256.hex bytes.toUTF8)),
    ("direct_imports", ← IO.ofExcept <| result.getObjVal? "direct_imports"),
    ("environment_modules", ← IO.ofExcept <| result.getObjVal? "environment_modules")]
  IO.FS.writeFile destination bytes
  IO.FS.writeFile (destination ++ ".receipt.json") (receipt.compress ++ "\n")

end LeanInformationAudit.CensusReceipt
