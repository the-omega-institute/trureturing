import LeanInformationAudit.Census.Membership

def main (args : List String) : IO Unit := do
  let [stream, request, destination] := args
    | throw <| IO.userError "expected stream, request, destination"
  LeanInformationAudit.CensusStream.membership stream request destination
