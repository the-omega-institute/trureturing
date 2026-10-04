import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.Contract.InterfaceGuard
import LeanInformationAudit.RuntimeInputs
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace LeanInformationAuditRegTests.ContractExactPolicy
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

universe u

theorem universeTarget (A : Type u) : A = A := rfl

def storedSignature : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature where
  Params := Seal
  State := fun _ => Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Unit
  Anchor := Unit
  finiteAnchor := inferInstance

def storedResult : storedSignature.Params := { rootId := `Stored, options := #[] }
def signatureAlias := storedSignature
def wrappedResult : Option storedSignature.Params := some storedResult

run_meta do
  let env := (← getEnv).setExporting false
  for (label, levels, accepted) in #[
      ("ValidTargetLevels", [Level.zero], true),
      ("MissingTargetLevels", [], false),
      ("ExtraTargetLevels", [Level.zero, Level.zero], false)] do
    let mut error := "accepted"
    try discard <| Decoder.checkTarget ``universeTarget (.const ``universeTarget levels)
    catch ex => error := ← ex.toMessageData.toString
    assertTest s!"policy.target.{label}"
      (if accepted then error == "accepted"
       else error.startsWith "unclassified_form:contract.target_statement:")

  for (label, source) in #[
      ("WrappedCommand", "set_option maxRecDepth 4096 in\nrun_meta Lean.logInfo \"message\""),
      ("WrappedRunCmd", "set_option maxRecDepth 4096 in\nrun_cmd pure ()"),
      ("UnknownAttribute", "attribute [unlistedForm] Nat"),
      ("UnknownDeclarationAttribute", "@[unlistedForm] def x : Nat := 0"),
      ("SuffixAttribute", "attribute [Other.instance] Nat"),
      ("AttributeArgument", "attribute [instance 100] Nat")] do
    let entries ← SourceAudit.parse env source "Reg.UnlistedForm"
    let error : String := match SourceAudit.auditRegCommands `Reg.UnlistedForm entries with
      | .error e => e | .ok _ => "accepted"
    assertTest s!"policy.reg.{label}"
      (error.startsWith "contract.reg:metaprogramming_not_allowed:")
    logInfo m!"CONTRACT_DIAGNOSTIC {label} {error}"
  for (label, source) in #[
      ("ByElab", "structure X where\n x : (by_elab pure (Lean.mkConst ``Nat))"),
      ("Tactic", "structure X where\n x : (by exact Nat)"),
      ("DoTerm", "structure X where\n x : (do pure 0)"),
      ("Quotation", "structure X where\n x : `(Nat)"),
      ("Default", "structure X where\n x : Nat := 0"),
      ("ParameterElaboration", "inductive X (T : (by_elab pure (Lean.mkConst ``Nat))) where\n | mk : X T")] do
    let entries ← SourceAudit.parse env source "InterfaceUnlistedForm"
    let error : String := match InterfaceGuard.audit env `InterfaceUnlistedForm entries with
      | .error e => e | .ok _ => "accepted"
    assertTest s!"policy.interface.{label}"
      (error.startsWith "contract.interface:command_not_allowed:")
    logInfo m!"CONTRACT_DIAGNOSTIC {label} {error}"

end LeanInformationAuditRegTests.ContractExactPolicy
