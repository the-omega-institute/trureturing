import LeanInformationAuditRegTests.ContractGuards

namespace LeanInformationAuditRegTests.ContractNegative
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

private def sourceRejected (label source expected : String) : MetaM Unit := do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `command source
  let error := match SourceAudit.audit stx ``Seal with
    | .ok _ => "accepted"
    | .error error => error
  assertTest label (error == expected)
  logInfo m!"CONTRACT_DIAGNOSTIC {label} {error}"

run_meta do
  assertTest "source.anonymous_head"
    (!SourceAudit.isHeadSpelling (mkIdent Name.anonymous) Name.anonymous)
  let diagnosticPrefix := "def exampleContract : LeanInformationAudit.Contract.Seal := "
  let value := "{ rootId := Lean.Name.anonymous, options := #[] }"
  sourceRejected "source.alias" "def x : Alias := { rootId := Lean.Name.anonymous, options := #[] }"
    "contract.discovery:type_alias_or_wrapper"
  sourceRejected "source.wrapper" "def x : Box LeanInformationAudit.Contract.Seal := wrapped"
    "contract.discovery:type_alias_or_wrapper"
  sourceRejected "source.parameters" "def x (n : Nat) : LeanInformationAudit.Contract.Seal := {}"
    "contract.discovery:term_parameters"
  sourceRejected "source.forall" "def x : Nat → LeanInformationAudit.Contract.Seal := fun _ => {}"
    "contract.discovery:forall"
  sourceRejected "source.lambda" (diagnosticPrefix ++ "fun _ => {}") "contract.discovery:lambda"
  sourceRejected "source.forwarding" (diagnosticPrefix ++ "other") "contract.discovery:forwarding_or_computed"
  sourceRejected "source.computed" (diagnosticPrefix ++ "(fun x => x) " ++ value)
    "contract.discovery:forwarding_or_computed"
  sourceRejected "source.update" (diagnosticPrefix ++ "{ other with rootId := Lean.Name.anonymous }")
    "contract.discovery:structure_update"
  sourceRejected "source.instance" "instance x : LeanInformationAudit.Contract.Seal := {}"
    "contract.discovery:instance"
  sourceRejected "source.opaque" "opaque x : LeanInformationAudit.Contract.Seal := {}"
    "contract.discovery:opaque"
  sourceRejected "source.unsafe" "unsafe def x : LeanInformationAudit.Contract.Seal := {}"
    "contract.discovery:unsafe"
  sourceRejected "source.abbrev" "abbrev x : LeanInformationAudit.Contract.Seal := {}"
    "contract.discovery:not_def"
  sourceRejected "source.where" "def x : LeanInformationAudit.Contract.Seal where\n rootId := Lean.Name.anonymous\n options := #[]"
    "contract.discovery:structure_literal"
  let mut error := "accepted"
  try
    discard <| Discovery.auditModule `Synthetic.sourceOnly
      "def extra : LeanInformationAudit.Contract.Seal := { rootId := Lean.Name.anonymous, options := #[] }"
  catch ex => error := ← ex.toMessageData.toString
  assertTest "inventory.source_without_compiled_entry"
    (error.startsWith "contract.discovery:compiled_inventory_missing")

def AliasType := Seal
def forwarded : Seal := { rootId := .anonymous, options := #[] }
def viaAlias : AliasType := forwarded
def asFunction (n : Nat) : Seal := { rootId := .num .anonymous n, options := #[] }
opaque hidden : Seal := { rootId := .anonymous, options := #[] }
unsafe def unsafeEntry : Seal := { rootId := .anonymous, options := #[] }
def relay : Seal := forwarded

run_meta do
  let mut sourceError := "accepted"
  try
    discard <| Discovery.auditModule `Synthetic.aliasOnly
      "def extra : LeanInformationAuditRegTests.ContractNegative.AliasType := { rootId := Lean.Name.anonymous, options := #[] }"
  catch ex => sourceError := ← ex.toMessageData.toString
  assertTest "inventory.alias_source_without_compiled_entry"
    (sourceError.startsWith "contract.discovery:compiled_inventory_missing")
  for (name, expected) in #[
      (``viaAlias, "contract.discovery:type_alias_or_wrapper"),
      (``asFunction, "contract.discovery:forall"),
      (``hidden, "contract.discovery:not_def"),
      (``unsafeEntry, "contract.discovery:unsafe"),
      (``relay, "contract.discovery:forwarding_or_computed")] do
    let info ← getConstInfo name
    let mut error := "accepted"
    try discard <| Discovery.checkDefinition info
    catch ex => error := ← ex.toMessageData.toString
    assertTest s!"compiled.{name.getString!}" (error.startsWith expected)
    logInfo m!"CONTRACT_DIAGNOSTIC compiled.{name.getString!} {error}"
  let mut noRange := (← getConstInfo ``forwarded).toConstantVal
  noRange := { noRange with name := `Synthetic.noRange }
  let value : DefinitionVal := { noRange with
    value := (← getConstInfo ``forwarded).value!,
    hints := .opaque, safety := .safe }
  addDecl (.defnDecl value)
  let mut openError := "accepted"
  try discard <| Discovery.checkDefinition (.defnInfo { value with value := .bvar 0 })
  catch ex => openError := ← ex.toMessageData.toString
  assertTest "compiled.open_term" (openError.startsWith "contract.discovery:open_term")
  let mut error := "accepted"
  try discard <| Discovery.requireRange noRange.name
  catch ex => error := ← ex.toMessageData.toString
  assertTest "compiled.missing_source_range" (error.startsWith "contract.discovery:source_range")
  let info := { value with levelParams := [`u, `v] }
  error := "accepted"
  try Decoder.rigidLevels info (.const `Synthetic.target [.param `v, .param `u])
  catch ex => error := ← ex.toMessageData.toString
  assertTest "compiled.permuted_universes" (error.startsWith "contract.discovery:rigid_universes")
  error := "accepted"
  try Decoder.rigidLevels info (.const `Synthetic.target [.param `u])
  catch ex => error := ← ex.toMessageData.toString
  assertTest "compiled.missing_universe" (error.startsWith "contract.discovery:rigid_universes")

def referencedName : Name := `ContractTests
def referencedSelection : SourceSelection := {
  owner := .anonymous, definition := none, coordinates := #[], readouts := #[] }
def referencedOptions : Array OptionSetting := #[]

run_meta do
  let rejects {α : Type} (label : String) (value : Except String α) (diagnosticPrefix : String) := do
    let error : String := match value with | .ok _ => "accepted" | .error error => error
    assertTest label (error.startsWith diagnosticPrefix)
    logInfo m!"CONTRACT_DIAGNOSTIC {label} {error}"
  rejects "literal.referenced_name" (Literal.name "name" (mkConst ``referencedName))
    "contract.literal:name:nonliteral"
  rejects "literal.referenced_selection" (Literal.sourceSelection (mkConst ``referencedSelection))
    "contract.literal:source_selection:nonliteral"
  rejects "literal.referenced_options" (Literal.options (mkConst ``referencedOptions))
    "contract.literal:options:nonliteral"
  rejects "literal.computed_array" (Literal.array "expected" (mkApp (mkConst ``Array.map) (mkNatLit 0)))
    "contract.literal:expected:nonliteral"
  rejects "literal.append_array" (Literal.array "expected" (mkConst ``Array.append))
    "contract.literal:expected:nonliteral"
  rejects "literal.filter_array" (Literal.array "expected" (mkConst ``Array.filter))
    "contract.literal:expected:nonliteral"
  rejects "literal.capture_statement" (Literal.optional "identity" (mkConst `RootCatalogs.captureStatement))
    "contract.literal:identity:nonliteral"
  rejects "literal.environment" (Literal.name "root" (mkConst ``getEnv))
    "contract.literal:root:nonliteral"
  rejects "literal.open" (Literal.name "open" (.bvar 0)) "contract.literal:open:nonliteral"

end LeanInformationAuditRegTests.ContractNegative
