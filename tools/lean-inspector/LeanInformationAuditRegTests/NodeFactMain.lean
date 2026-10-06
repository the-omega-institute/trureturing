import LeanInformationAuditRegTests.NodeFacts
import LeanInformationAudit.Registry.Repository

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let fixturePath ← LeanInformationAudit.Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  Lean.searchPathRef.modify (fixturePath :: ·)
  LeanInformationAuditRegTests.NodeFacts.check
