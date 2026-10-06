import Lean

namespace LeanInformationAudit.CensusStructure

/-- Inspector remains self-contained and owns all per-kind dependency rules.
The subprocess streams detached records one module at a time; its failures
propagate to the report-only sidecar's unavailable diagnostic. -/
def scan (manifest destination mode : String) : IO Unit := do
  let child ← IO.Process.spawn { cmd := "lean", args := #["--run",
    "tools/lean-inspector/Inspector.lean", "--dependencies", manifest, destination, mode] }
  let status ← child.wait
  unless status == 0 do
    throw <| IO.userError s!"Inspector dependencies exited {status}"

end LeanInformationAudit.CensusStructure
