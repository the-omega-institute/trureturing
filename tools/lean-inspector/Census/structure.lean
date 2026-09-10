import LeanInformationAudit.Census.StructureReader

unsafe def main (args : List String) : IO Unit := do
  let [manifest, destination, mode] := args
    | throw <| IO.userError "expected manifest, destination, mode"
  LeanInformationAudit.CensusStructure.scan manifest destination mode
