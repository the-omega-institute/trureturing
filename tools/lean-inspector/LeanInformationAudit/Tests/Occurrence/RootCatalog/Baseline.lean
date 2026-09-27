import LeanInformationAudit.Tests.Occurrence.RootCatalog.Snapshot

open LeanInformationAudit LeanInformationAudit.Tests.Occurrence.RootCatalog
open LeanInformationAudit.Tests.Occurrence.JointImport

run_cmd RootCatalogs.declare baselineContract

register_information_theorem shared in arena
  primitives readout.toPrimitiveBundle
  realization inline readout := by exact ⟨Iff.rfl⟩

#seal_information_theory
