import LeanInformationAuditRegAnalysis.AuricFib.Report

open Lean LeanInformationAudit.AuricFib

/-- Each independent request retains its complete SPEC 9 output and rejection. -/
def main (args : List String) : IO UInt32 := do
  let batch := args == ["--batch"]
  if !args.isEmpty && !batch then
    IO.println (unavailableReport "refuted"
      "expected no arguments or --batch, with JSON on stdin" "invalid-input").compress
    return 2
  try
    let stdin ← IO.getStdin
    let text ← stdin.readToEnd
    let parsed := Json.parse text
    let requests := if batch then parsed >>= Json.getArr? else parsed.map (fun r => #[r])
    match requests with
    | .error reason =>
      IO.println (unavailableReport "refuted" reason "invalid-input").compress
      return 2
    | .ok requests =>
      if requests.isEmpty then
        IO.println (unavailableReport "refuted" "empty analysis batch" "invalid-input").compress
        return 2
      let mut reports := #[]
      let mut exitCode : UInt32 := 0
      for request in requests do
        match analyze request with
        | .ok report => reports := reports.push report
        | .error reason =>
          reports := reports.push (unavailableReport "refuted" reason "invalid-input")
          exitCode := 2
      IO.println (if batch then Json.arr reports else reports[0]!).compress
      return exitCode
  catch error =>
    IO.println (unavailableReport "deferred" s!"execution error: {error}" "unavailable").compress
    return 1
