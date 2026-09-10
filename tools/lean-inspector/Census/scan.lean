import LeanInformationAudit.Census.Stream

unsafe def main (args : List String) : IO Unit := do
  let [manifest, request, destination] := args
    | throw <| IO.userError "expected manifest, request, destination"
  LeanInformationAudit.CensusStream.scan manifest request destination
