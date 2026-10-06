import LeanInformationAuditRegTests.ContractFixtures
import LeanInformationAuditRegTests.ContractWitnessFixture
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms

namespace LeanInformationAuditRegTests.CompiledDiscovery
open Lean LeanInformationAudit

/-- Exercise the standalone artifact-reader boundary on every contract input
kind, including an indexed partial-slot family and rigid theorem universes. -/
unsafe def readFixtures (start limit : Nat) : IO Unit := do
  let fixturePath ← Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  let saved ← searchPathRef.get
  searchPathRef.set (fixturePath :: saved)
  try
    let owners := #[`LeanInformationAuditRegTests.ContractFixtures,
      `LeanInformationAuditRegTests.ContractWitnessFixture]
    let reader ← IO.mkRef ({} : RawArtifacts.Store)
    for owner in owners do RawArtifacts.loadModule owner reader
    let store ← reader.get
    let context : Contract.CompiledExpressions.Context := {
      find := (store.constants[·]?)
      heartbeatStart := start
      heartbeatLimit := limit }
    let closures ← IO.mkRef ({} : CompiledAxioms.AxiomClosureState)
    let snapshot ← Contract.Discovery.discoverCompiled #[] owners context
      (fun owner => return (← store.getModule owner).constants)
      (CompiledAxioms.collectAxiomsShared context.find closures)
    unless snapshot.registrations.size == 20 && snapshot.enrollments.size == 1 &&
        snapshot.roots.size == 1 && snapshot.seals.size == 1 do
      throw <| IO.userError "compiled.discovery:input_inventory"
    let some (_, partialRow) := snapshot.registrations.find?
        (·.2.input.entry.unitName == `ContractTests.partialSensitivity.unit)
      | throw <| IO.userError "compiled.discovery:partial_slot_input"
    unless partialRow.input.entry.compiledMathematics.any (fun evidence =>
        evidence.partialReadouts == some #[true, false] && evidence.partialAnchors == some #[]) do
      throw <| IO.userError "compiled.discovery:partial_slot_support"
    for index in [:5] do
      let name := owners[0]!.str s!"source{index}"
      let some definition := snapshot.definitions.find? (·.info.name == name)
        | throw <| IO.userError s!"compiled.discovery:rigid_target:{name}"
      let target := definition.info.type.getAppArgs[1]!
      unless target.constLevels! == definition.info.levelParams.map Level.param do
        throw <| IO.userError s!"compiled.discovery:rigid_levels:{name}"
    IO.println "[PASS] compiled discovery reads 20 registrations, 1 enrollment, 1 root and 1 seal"
  finally searchPathRef.set saved

run_meta do
  readFixtures (← Lean.getInitHeartbeats) (← Lean.getMaxHeartbeats)

end LeanInformationAuditRegTests.CompiledDiscovery
