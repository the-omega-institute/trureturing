import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.Contract.InterfaceGuard
import D5.S3.ConceptDynamics.InformationEscape.Arena

namespace LeanInformationAuditRegTests.ContractGuards
open Lean Meta Elab Command

def assertTest (label : String) (ok : Bool) : MetaM Unit := do
  if ok then logInfo m!"[PASS] {label}"
  else logError m!"[FAIL] {label}"

run_meta do
  let env := (← getEnv).setExporting false
  let interfaceModules := env.header.moduleNames.filter
    ((`LeanInformationAuditInterface.Contract).isPrefixOf ·)
  assertTest "interface.contract_modules" (interfaceModules.size >= 4)
  for owner in interfaceModules do
    let source ← IO.FS.readFile (← LeanInformationAudit.Repository.source
      ("tools/lean-inspector-interface/" ++ owner.toString.replace "." "/" ++ ".lean"))
    let entries ← LeanInformationAudit.Contract.SourceAudit.parse env source owner.toString
    let result := LeanInformationAudit.Contract.InterfaceGuard.audit env owner entries
    assertTest s!"interface.types_only.{owner.getString!}" result.isOk
    if let .error error := result then logInfo m!"CONTRACT_DIAGNOSTIC {error}"
  for (label, source) in #[
      ("variable", "variable (n : Nat)"),
      ("attribute", "attribute [simp] Nat"),
      ("set_option", "set_option pp.universes true"),
      ("run_meta", "run_meta pure ()"),
      ("initialize", "initialize x : IO Unit := pure ()"),
      ("macro", "macro \"x\" : command => `(skip)") ] do
    let entries ← LeanInformationAudit.Contract.SourceAudit.parse env source "InterfacePolicyNegative"
    let result := LeanInformationAudit.Contract.InterfaceGuard.audit env
      `InterfacePolicyNegative entries
    assertTest s!"interface.command_allowlist.{label}" (match result with
      | .error error => error.startsWith "contract.interface:command_not_allowed:"
      | .ok _ => false)
  let letIssue := LeanInformationAudit.Contract.SourceAudit.resultTypeIssue env
    (.letE `hidden (.sort .zero) (.sort .zero) (.sort .zero) false)
  assertTest "reg.result_type.let_rejected"
    (letIssue.any (·.startsWith "contract.discovery:result_type_let"))
  let letEntries ← LeanInformationAudit.Contract.SourceAudit.parse env
    "def x : (let T := Nat; T) := 0" "Reg.ResultTypeLetSyntax"
  let letSyntaxIssue := letEntries.find? (·.sourceName == some `x) |>.bind fun entry =>
    LeanInformationAudit.Contract.SourceAudit.sourceResultTypeIssue entry.command
  assertTest "reg.result_type.source_let_rejected"
    (letSyntaxIssue.any (·.startsWith "contract.discovery:result_type_let"))
  let projection := Expr.proj ``LeanInformationAudit.Contract.TypeRef 1
    (.const ``LeanInformationAudit.Contract.TypeRef [])
  assertTest "reg.result_type.stored_sort_projection_rejected"
    ((LeanInformationAudit.Contract.SourceAudit.resultTypeIssue env projection).any
      (·.startsWith "contract.discovery:result_type_projection:"))
  let allowedProjection := Expr.proj
    ``D5.S3.ConceptDynamics.InformationEscape.Arena 0
    (.const ``D5.S3.ConceptDynamics.InformationEscape.Arena [])
  assertTest "reg.result_type.allowlisted_arena_projection"
    ((LeanInformationAudit.Contract.SourceAudit.resultTypeIssue env allowedProjection).isNone)
  for (label, source) in #[
      ("run_meta", "run_meta pure ()"),
      ("macro", "macro \"x\" : command => `(skip)"),
      ("notation", "notation \"x\" => 1"),
      ("run_cmd", "run_cmd do pure ()") ] do
    let entries ← LeanInformationAudit.Contract.SourceAudit.parse env source "Reg.PolicyNegative"
    let result := LeanInformationAudit.Contract.SourceAudit.auditRegCommands
      `Reg.PolicyNegative entries
    assertTest s!"reg.metaprogramming_ban.{label}" (match result with
      | .error error => error.startsWith "contract.reg:metaprogramming_not_allowed:"
      | .ok _ => false)
  for (kind, source) in #[
      ("def", "def x : Nat := 17"),
      ("theorem", "theorem x : True := by trivial"),
      ("abbrev", "abbrev x : Nat := 17"),
      ("opaque", "opaque x : Nat := 17"),
      ("instance", "instance x : Inhabited Nat := ⟨17⟩"),
      ("axiom", "axiom x : Nat")] do
    let entries ← LeanInformationAudit.Contract.SourceAudit.parse env source "InterfaceNegative"
    let result := LeanInformationAudit.Contract.InterfaceGuard.auditSource entries
    assertTest s!"interface.authored_non_type.{kind}" (match result with
      | .error error => error.startsWith "contract.interface:authored_non_type:"
      | .ok _ => false)
  let structures := #[
    ``LeanInformationAudit.Contract.Ref, ``LeanInformationAudit.Contract.OptionSetting,
    ``LeanInformationAudit.Contract.ReadoutSelection,
    ``LeanInformationAudit.Contract.DefinitionSelection,
    ``LeanInformationAudit.Contract.SourceSelection,
    ``LeanInformationAudit.Contract.Registration,
    ``LeanInformationAudit.Contract.TypeRef,
    ``LeanInformationAudit.Contract.TemplateEnrollment,
    ``LeanInformationAudit.Contract.ExpectedOccurrence,
    ``LeanInformationAudit.Contract.RootCatalogData,
    ``LeanInformationAudit.Contract.RootCatalog,
    ``LeanInformationAudit.Contract.ExpectedDeclaration,
    ``LeanInformationAudit.Contract.Seal]
  let mut fields : Nat := 0
  for structureName in structures do
    let names := getStructureFields env structureName
    assertTest s!"defaults.structure.{structureName}" (!names.isEmpty)
    for field in names do
      fields := fields + 1
      assertTest s!"defaults.field.{structureName}.{field}"
        ((getEffectiveDefaultFnForField? env structureName field).isNone)
  logInfo m!"CONTRACT_DEFAULT_FIELDS {fields}"
  let mut pending : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`LeanInformationAudit.Contract).isPrefixOf name then pending := pending.push name
  let roots := pending.size
  let mut seen : NameSet := {}
  let mut forbidden : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if #[`Lean.Meta.evalExpr, `Lean.evalConst, `Lean.evalConstCheck,
        `Lean.evalConstCheck', `Lean.Meta.evalExprCore].contains name then
      forbidden := forbidden.push name
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  assertTest "compiled_guard_native" forbidden.isEmpty
  logInfo m!"CONTRACT_NATIVE_DEPENDENCIES roots={roots} visited={seen.size} forbidden={forbidden}"

end LeanInformationAuditRegTests.ContractGuards
