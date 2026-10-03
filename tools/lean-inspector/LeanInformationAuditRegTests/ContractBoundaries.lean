import LeanInformationAudit.Contract.Discovery
import LeanInformationAuditRegTests.ContractBoundaryFixtures.MathematicalCompanion
import LeanInformationAuditRegTests.ContractBoundaryFixtures.HelperBody
import LeanInformationAuditRegTests.ContractBoundaryFixtures.MathCompanion
import LeanInformationAuditRegTests.ContractBoundaryFixtures.MathAux
import LeanInformationAuditRegTests.ContractBoundaryFixtures.RegCompanion
import LeanInformationAuditRegTests.ContractBoundaryFixtures.MathParameter
import LeanInformationAuditRegTests.ContractBoundaryFixtures.Constructors
import LeanInformationAuditRegTests.ContractBoundaryFixtures.LiteralGrammar
import LeanInformationAuditRegTests.ContractBoundaryFixtures.SectionUnused
import LeanInformationAuditRegTests.ContractBoundaryFixtures.SectionUsed
import LeanInformationAuditRegTests.ContractBoundaryFixtures.BuiltinMacro
import LeanInformationAuditRegTests.ContractBoundaryFixtures.MacroImport

import LeanInformationAuditRegTests.ContractBoundaryFixtures.TermMacro
import LeanInformationAuditRegTests.ContractBoundaryFixtures.TermElab
import LeanInformationAuditRegTests.ContractBoundaryFixtures.TermNotation
import LeanInformationAuditRegTests.ContractBoundaryFixtures.TermElabRules
import LeanInformationAuditRegTests.ContractBoundaryFixtures.IntInstance
import LeanInformationAuditRegTests.ContractBoundaryFixtures.NegInstance
import LeanInformationAuditRegTests.ContractBoundaryFixtures.LocalBuiltinMacro
import LeanInformationAuditRegTests.ContractBoundaryFixtures.DelegateForgery
namespace LeanInformationAuditRegTests.ContractBoundaries
open Lean Meta Elab Command LeanInformationAudit.Contract
private def check (label : String) (ok : Bool) : MetaM Unit := do
  if ok then logInfo m!"[PASS] {label}" else logError m!"[FAIL] {label}"
run_meta do
  let errorMathematicalCompanion ← try
    discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.MathematicalCompanion]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  check "discovery.reference.MathematicalCompanion"
    (errorMathematicalCompanion.startsWith "contract.reg:contract_reference_outside_entry:")
  let errorHelperBody ← try
    discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.HelperBody]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  check "discovery.reference.HelperBody"
    (errorHelperBody.startsWith "contract.reg:contract_reference_outside_entry:")
  let errorMathCompanion ← try
    discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.MathCompanion]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  check "discovery.reference.MathCompanion"
    (errorMathCompanion.startsWith "contract.reg:contract_reference_outside_entry:")
  let errorMathAux ← try
    discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.MathAux]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  check "discovery.reference.MathAux"
    (errorMathAux.startsWith "contract.reg:contract_reference_outside_entry:")
  let errorRegCompanion ← try
    discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.RegCompanion]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  check "discovery.reference.RegCompanion"
    (errorRegCompanion.startsWith "contract.reg:contract_reference_outside_entry:")
  let errorMathParameter ← try
    discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.MathParameter]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  check "discovery.reference.MathParameter"
    (errorMathParameter.startsWith "contract.reg:contract_reference_outside_entry:")
  try
    let snapshot ← Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.Constructors]
    check "discovery.positive.Constructors" (snapshot.definitions.size == 1)
  catch ex =>
    check "discovery.positive.Constructors" false
    logInfo m!"CONTRACT_DIAGNOSTIC {← ex.toMessageData.toString}"
  try
    let snapshot ← Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.LiteralGrammar]
    check "discovery.positive.LiteralGrammar" (snapshot.definitions.size == 1)
  catch ex =>
    check "discovery.positive.LiteralGrammar" false
    logInfo m!"CONTRACT_DIAGNOSTIC {← ex.toMessageData.toString}"
  try
    let snapshot ← Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.SectionUnused]
    check "discovery.positive.SectionUnused" (snapshot.definitions.size == 1)
  catch ex =>
    check "discovery.positive.SectionUnused" false
    logInfo m!"CONTRACT_DIAGNOSTIC {← ex.toMessageData.toString}"
  let mut errorSectionUsed := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.SectionUsed]
  catch ex => errorSectionUsed := ← ex.toMessageData.toString
  check "discovery.negative.SectionUsed" (errorSectionUsed.startsWith "contract.reg:contract_reference_outside_entry:")
  logInfo m!"CONTRACT_DIAGNOSTIC SectionUsed {errorSectionUsed}"
  let mut errorBuiltinMacro := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.BuiltinMacro]
  catch ex => errorBuiltinMacro := ← ex.toMessageData.toString
  check "discovery.negative.BuiltinMacro" (errorBuiltinMacro.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC BuiltinMacro {errorBuiltinMacro}"
  let mut errorMacroImport := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.MacroImport]
  catch ex => errorMacroImport := ← ex.toMessageData.toString
  check "discovery.negative.MacroImport" (errorMacroImport.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC MacroImport {errorMacroImport}"
  let mut errorTermMacro := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.TermMacro]
  catch ex => errorTermMacro := ← ex.toMessageData.toString
  check "discovery.negative.TermMacro" (errorTermMacro.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC TermMacro {errorTermMacro}"
  let mut errorTermElab := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.TermElab]
  catch ex => errorTermElab := ← ex.toMessageData.toString
  check "discovery.negative.TermElab" (errorTermElab.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC TermElab {errorTermElab}"
  let mut errorTermNotation := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.TermNotation]
  catch ex => errorTermNotation := ← ex.toMessageData.toString
  check "discovery.negative.TermNotation" (errorTermNotation.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC TermNotation {errorTermNotation}"
  let mut errorTermElabRules := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.TermElabRules]
  catch ex => errorTermElabRules := ← ex.toMessageData.toString
  check "discovery.negative.TermElabRules" (errorTermElabRules.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC TermElabRules {errorTermElabRules}"
  let mut errorIntInstance := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.IntInstance]
  catch ex => errorIntInstance := ← ex.toMessageData.toString
  check "discovery.negative.IntInstance" (errorIntInstance.startsWith "contract.literal:option.int:nonliteral:")
  logInfo m!"CONTRACT_DIAGNOSTIC IntInstance {errorIntInstance}"
  let mut errorNegInstance := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.NegInstance]
  catch ex => errorNegInstance := ← ex.toMessageData.toString
  check "discovery.negative.NegInstance" (errorNegInstance.startsWith "contract.literal:option.int:nonliteral:")
  logInfo m!"CONTRACT_DIAGNOSTIC NegInstance {errorNegInstance}"
  let mut errorLocalBuiltinMacro := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.LocalBuiltinMacro]
  catch ex => errorLocalBuiltinMacro := ← ex.toMessageData.toString
  check "discovery.negative.LocalBuiltinMacro" (errorLocalBuiltinMacro.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC LocalBuiltinMacro {errorLocalBuiltinMacro}"
  let mut errorDelegateForgery := "accepted"
  try discard <| Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.DelegateForgery]
  catch ex => errorDelegateForgery := ← ex.toMessageData.toString
  check "discovery.negative.DelegateForgery" (errorDelegateForgery.startsWith "contract.source_literal:term_expander:")
  logInfo m!"CONTRACT_DIAGNOSTIC DelegateForgery {errorDelegateForgery}"
  try
    let snapshot ← Discovery.discover #[`LeanInformationAuditRegTests.ContractFixtures]
    check "discovery.positive.LegacyPayloads" (!snapshot.registrations.isEmpty)
  catch ex =>
    check "discovery.positive.LegacyPayloads" false
    logInfo m!"CONTRACT_DIAGNOSTIC {← ex.toMessageData.toString}"
  try
    let snapshot ← Discovery.discover #[`LeanInformationAuditRegTests.ContractBoundaryFixtures.LiteralGrammar]
    let some (_, sealInput) := snapshot.seals[0]? | throwError "grammar seal missing"
    let options := sealInput.options
    for (key, expected) in #[(`nat.annotated, DataValue.ofNat 7), (`nat.chain, .ofNat 2),
        (`int.positive, .ofInt 7), (`int.negative, .ofInt (-7)), (`int.negZero, .ofInt 0),
        (`int.ofNat, .ofInt 1), (`int.negSucc, .ofInt (-5)),
        (`int.ofNatMethod, .ofInt 8), (`int.negMethod, .ofInt (-8))] do
      check s!"discovery.literal.{key}" (options.find? key == some expected)
  catch ex =>
    check "discovery.literal.values" false
    logInfo m!"CONTRACT_DIAGNOSTIC {← ex.toMessageData.toString}"
end LeanInformationAuditRegTests.ContractBoundaries
