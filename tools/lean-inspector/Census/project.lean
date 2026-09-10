import LeanInformationAudit.Census.Report

open Lean LeanInformationAudit LeanInformationAudit.DispositionCensus

/-- Rows have already been scoped by membership. Parse and account for one row
at a time; the emitter expands its shared, receipt-bound scope by root. -/
def main (args : List String) : IO Unit := do
  let [inputPath, destination] := args | throw <| IO.userError "expected input and output"
  let input ← IO.ofExcept <| Json.parse (← IO.FS.readFile inputPath)
  let head ← IO.ofExcept <| input.getObjValAs? String "head"
  let rowsPath ← IO.ofExcept <| input.getObjValAs? String "rows_file"
  let rowsIn ← IO.FS.Handle.mk rowsPath .read
  let rowsOut ← IO.FS.Handle.mk (destination ++ ".rows.jsonl") .write
  let mut counts : Counts := {}
  repeat
    let line ← rowsIn.getLine
    if line.isEmpty then break
    let row ← IO.ofExcept <| Json.parse line
    let entry ← IO.ofExcept <| parseRow row (some ⟨#[], true⟩)
    if let .observed value := entry.2 then
      if value.queryCompleted then IO.ofExcept <| checkObservationStatus head value
    counts := counts.addEntry entry
    let json := dispositionRowJson entry
    let json := if let .observed _ := entry.2 then
      json.setObjVal! "payload" ((← IO.ofExcept <| json.getObjVal? "payload").setObjVal!
        "import_scope" Json.null) else json
    rowsOut.putStrLn (Json.mkObj [("sort_name", toJson entry.1.theoremName.toString),
      ("row", json)]).compress
  rowsOut.flush
  IO.FS.writeFile destination (Json.mkObj [("counts", toJson counts)]).compress
