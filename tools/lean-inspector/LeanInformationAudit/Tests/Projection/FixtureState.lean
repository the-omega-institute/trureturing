import LeanInformationAudit.ProjectionSchema

namespace LeanInformationAudit.Tests.Projection

open Lean

initialize projectionFixtureStore : SimplePersistentEnvExtension KernelProjectionRecord
    (Array KernelProjectionRecord) ← registerSimplePersistentEnvExtension {
  addEntryFn := Array.push
  addImportedFn := fun entries => entries.foldl (· ++ ·) #[] }

end LeanInformationAudit.Tests.Projection
