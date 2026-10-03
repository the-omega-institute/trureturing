import LeanInformationAudit.Tests.Occurrence.RootCatalog.Snapshot
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open LeanInformationAudit LeanInformationAudit.Tests.Occurrence.RootCatalog
open LeanInformationAudit.Tests.Occurrence.JointImport

run_cmd RootCatalogs.declare baselineContract

test_assess in register_information_theorem shared in arena
  primitives readout.toPrimitiveBundle
  realization inline readout := by exact ⟨Iff.rfl⟩

test_assess in #seal_information_theory
