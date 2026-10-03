import LeanInformationAuditRegTests.ContractGuards
import LeanInformationAuditRegTests.ContractReferenceFixtures.AuthoredAuxiliary
import LeanInformationAuditRegTests.ContractReferenceFixtures.Auxiliary
import LeanInformationAuditRegTests.ContractReferenceFixtures.ComputedSignature
import LeanInformationAuditRegTests.ContractReferenceFixtures.NestedCarrier
import LeanInformationAuditRegTests.ContractReferenceFixtures.OptionPayload
import LeanInformationAuditRegTests.ContractReferenceFixtures.Ordinary
import LeanInformationAuditRegTests.ContractReferenceFixtures.Projection
import LeanInformationAuditRegTests.ContractReferenceFixtures.PrimitiveProjection
import LeanInformationAuditRegTests.ContractReferenceFixtures.RefPayload
import LeanInformationAuditRegTests.ContractReferenceFixtures.SigmaPayload
import LeanInformationAuditRegTests.ContractReferenceFixtures.StoredType
import LeanInformationAuditRegTests.ContractReferenceFixtures.TypeAlias
import LeanInformationAuditRegTests.ContractReferenceFixtures.TypeLambda
import LeanInformationAuditRegTests.ContractReferenceFixtures.TypeLet

namespace LeanInformationAuditRegTests.ContractReferences
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  for fixture in #["AuthoredAuxiliary", "ComputedSignature", "NestedCarrier", "OptionPayload", "Projection", "PrimitiveProjection", "RefPayload", "SigmaPayload", "StoredType", "TypeAlias", "TypeLambda", "TypeLet"] do
    let owner := (`LeanInformationAuditRegTests.ContractReferenceFixtures).str fixture
    let error ← try
      discard <| Discovery.discoverWithStructure #[] #[owner]
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"reference.negative.{fixture}"
      (error.startsWith "contract.reg:contract_reference_outside_entry:")
    logInfo m!"CONTRACT_DIAGNOSTIC reference.{fixture} {error}"
  for fixture in #["Ordinary", "Auxiliary"] do
    let owner := (`LeanInformationAuditRegTests.ContractReferenceFixtures).str fixture
    try
      let result ← Discovery.discoverWithStructure #[] #[owner]
      assertTest s!"reference.positive.{fixture}"
        (if fixture == "Ordinary" then result.definitions.isEmpty else result.definitions.size == 2)
    catch ex =>
      assertTest s!"reference.positive.{fixture}" false
      logInfo m!"CONTRACT_DIAGNOSTIC {← ex.toMessageData.toString}"
  let auxiliary ← getConstInfo `ContractReferenceFixtures.Auxiliary.entry.eq_1
  assertTest "reference.positive.compiler_equation_has_interface_references"
    (!(SourceAudit.directInterfaceReferences (← getEnv) auxiliary).isEmpty)

end LeanInformationAuditRegTests.ContractReferences
