import LeanInformationAuditRegTests.ContractFixtures
import LeanInformationAuditRegTests.ContractWitnessFixture
import LeanInformationAuditRegTests.ContractGuards

namespace LeanInformationAuditRegTests.ContractDiscovery
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let result ← Discovery.discoverWithStructure #[] #[`LeanInformationAuditRegTests.ContractFixtures] fun owner =>
    LeanInformationAudit.Repository.source
      ("tools/lean-inspector/" ++ owner.toString.replace "." "/" ++ ".lean")
  assertTest "discovery.catalog_expected_only"
    (result.registrations.size == 12 && result.enrollments.size == 1 &&
      result.roots.size == 1 && result.seals.size == 1)
  assertTest "discovery.private_noncomputable"
    (result.definitions.any (fun d => isPrivateName d.info.name))
  for n in [:5] do
    let name := (`LeanInformationAuditRegTests.ContractFixtures).str s!"source{n}"
    let some definition := result.definitions.find? (·.info.name == name)
      | throwError "setup: source fixture missing"
    let target := definition.info.type.getAppArgs[1]!
    let targetInfo ← getConstInfo target.constName!
    assertTest s!"discovery.rigid_universes.{n}"
      (definition.info.levelParams == targetInfo.levelParams &&
        target.constLevels! == definition.info.levelParams.map Level.param)
  let some enrollment := result.definitions.find?
      (·.info.name == `LeanInformationAuditRegTests.ContractFixtures.enrollment)
    | throwError "setup: enrollment fixture missing"
  assertTest "discovery.enrollment_five_universes"
    (enrollment.info.levelParams == [`t, `s, `r, `o, `a])
  let some finite := result.registrations.find? (·.2.input.entry.unitName == `ContractTests.finite.unit)
    | throwError "setup: finite source fixture missing"
  assertTest "decoder.finite_source_cross_combination"
    (finite.2.input.declaration.any fun d => d.escapeInput.finiteBridge.isSome &&
      d.sourceRecord == some `Reg.Support.LegacyRelations.Preemption.registration &&
      d.escapeInput.sourceSelection.any (fun s => s.readouts.size == 1) &&
      d.escapeInput.openContinuation)
  let some generated := result.registrations.find?
      (·.2.input.entry.unitName == `ContractTests.generatedLegacy.unit)
    | throwError "setup: generated fixture missing"
  assertTest "decoder.generated_occurrence_named_source"
    (generated.2.generated && !generated.2.input.entry.localRegistrationNames &&
      generated.2.input.entry.realizationName == `ContractTests.generatedLegacy.bridge &&
      generated.2.input.realizationSource.isSome &&
      generated.2.input.declaration.any (fun d => d.escapeInput.fromObject.isSome))
  let some continued := result.registrations.find?
      (·.2.input.entry.unitName == `ContractTests.continuingLegacy.unit)
    | throwError "setup: continuation fixture missing"
  assertTest "decoder.continuation_proof_term"
    (continued.2.input.declaration.any (fun d => d.escapeInput.continuation.isSome))
  assertTest "decoder.options_literal_values"
    (generated.2.input.options.get `maxHeartbeats (0 : Nat) == 2000000 &&
      generated.2.input.options.getBool `pp.unicode.fun)
  assertTest "decoder.expected_statement_capture"
    (result.roots[0]!.2.source[0]!.capturedStatement.isSome &&
      result.roots[0]!.2.expected[0]!.statementIdentity == "sha256:fixture")
  let witness ← Discovery.discoverWithStructure #[] #[`LeanInformationAuditRegTests.ContractWitnessFixture] fun owner =>
    LeanInformationAudit.Repository.source
      ("tools/lean-inspector/" ++ owner.toString.replace "." "/" ++ ".lean")
  let some (_, row) := witness.registrations[0]? | throwError "setup: witness"
  assertTest "decoder.witness_positive_variation_sensitivity"
    (witness.registrations.size == 1 && row.positive.isSome &&
      row.variation.isSome &&
      !row.input.entry.sensitivityWitness.isAnonymous &&
      row.input.declaration.any (fun d =>
        d.escapeInput.fromObject.isSome && d.escapeInput.openContinuation))

  let rows := result.registrations ++ witness.registrations
  let axes := rows.map fun (_, r) =>
    let declaration := r.input.declaration
    (if r.input.entry.sourceBound then "source" else if r.positive.isSome then "witness" else "legacy",
      r.generated, r.input.entry.localRegistrationNames,
      declaration.any (fun d => d.escapeInput.finiteBridge.isSome),
      declaration.any (fun d => d.escapeInput.fromObject.isSome),
      declaration.any (fun d => d.escapeInput.continuation.isSome))
  let combinations := #[
    ("source", false, false, false, false, false),
    ("legacy", false, true, false, true, false),
    ("legacy", true, true, false, true, false),
    ("legacy", false, true, false, false, false),
    ("legacy", true, false, false, true, true),
    ("legacy", true, false, false, true, false),
    ("witness", false, true, false, true, false),
    ("legacy", false, true, true, false, false),
    ("legacy", false, true, false, true, true)]
  assertTest "decoder.census_nine_cross_combinations" (combinations.all axes.contains)
  assertTest "decoder.census_descriptor_all" (rows.all fun (_, r) =>
    r.input.declaration.any (fun d => d.descriptor.isSome))
  logInfo m!"CONTRACT_AXIS_COMBINATIONS {combinations.size}"

end LeanInformationAuditRegTests.ContractDiscovery
