import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.Contract.InterfaceGuard
import LeanInformationAuditInterface.Store
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
      ("QuotedName", "run_cmd do let _ : Lean.Name := `LeanInformationAudit.RootCatalogs.declare; pure ()"),
      ("UnusedReference", "run_cmd do let _ := LeanInformationAudit.RootCatalogs.declare; pure ()"),
      ("SuffixMatch", "run_cmd Other.RootCatalogs.declare {}"),
      ("ExtraStatement", "run_cmd do LeanInformationAudit.RootCatalogs.declare {}; pure ()"),
      ("RunMetaReference", "run_meta do let _ := LeanInformationAudit.RootCatalogs.declare; pure ()"),
      ("RunElabReference", "run_elab do let _ := LeanInformationAudit.RootCatalogs.declare; pure ()"),
      ("ArchitectureQuotedName", "run_meta do let _ : Lean.Name := `LeanInformationAudit.RootCatalogs.declare; Lean.logInfo \"message\""),
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
  let owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
  for (label, source) in #[
      ("ExistingNotation", "local notation \"F\" => Nat.fib"),
      ("ChangedNotationToken", "local notation \"G\" => Nat.fib"),
      ("ChangedNotationTerm", "local notation \"F\" => Nat.succ"),
      ("MetadataNotation", "local notation \"false\" => Bool.true"),
      ("DuplicateNotation", "local notation \"F\" => Nat.fib\nlocal notation \"F\" => Nat.fib")] do
    let entries ← SourceAudit.parse env source owner.toString
    let result := SourceAudit.auditRegCommands owner entries
    assertTest s!"policy.notation.{label}"
      (if label == "ExistingNotation" then result.isOk else !result.isOk)

run_meta do
  let env := (← getEnv).setExporting false
  let notationText := "local notation \"ζ\" => riemannZeta\nlocal notation \"ζ'\" => deriv ζ\nlocal notation \"𝓜\" => mellin"
  for leaf in #["PntContourBound", "PntLongVertical", "PntShortContour", "PntSmoothing", "PntTail"] do
    let owner := `Reg.D5.S3.Weil.PrimeNumberTheorem ++ leaf.toName
    for (label, source, accepted) in #[
        ("distinct", notationText, true),
        ("duplicate", notationText ++ "\nlocal notation \"ζ\" => riemannZeta", false),
        ("changed", "local notation \"ζ\" => Nat", false)] do
      let entries ← SourceAudit.parse env source owner.toString
      let result := SourceAudit.auditRegCommands owner entries
      assertTest s!"policy.notation.pinned.{leaf}.{label}" (result.isOk == accepted)
    let entries ← SourceAudit.parse env notationText owner.toString
    assertTest s!"policy.notation.pinned.{leaf}.other_owner"
      (!(SourceAudit.auditRegCommands `Reg.UnlistedForm entries).isOk)

end LeanInformationAuditRegTests.ContractExactPolicy
