import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAudit.Contract.SourceAudit

namespace LeanInformationAuditRegTests.ContractInputLimits
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

private def wrappers : Array (String × (String → String)) := #[
  ("top", id), ("in", fun s => "open Nat in\n" ++ s),
  ("option", fun s => "set_option maxRecDepth 4096 in\n" ++ s),
  ("mutual", fun s => "mutual\n" ++ s ++ "\nend"),
  ("nested", fun s => "set_option maxRecDepth 4096 in\nopen Nat in\nmutual\n" ++ s ++ "\nend")]

run_meta do
  let env := (← getEnv).setExporting false
  let owner := `Reg.InputLimits
  for (name, value, wrong) in #[
      ("autoImplicit", "false", "0"), ("relaxedAutoImplicit", "true", "0"),
      ("backward.isDefEq.respectTransparency", "false", "0"),
      ("backward.isDefEq.respectTransparency.types", "true", "0"),
      ("maxHeartbeats", "200000", "true"), ("maxRecDepth", "4096", "false"),
      ("trace.InformationRegistration.check", "false", "0"),
      ("maxSynthPendingDepth", "64", "true")] do
    for (label, val, accepted) in #[("literal", value, true), ("type", wrong, false)] do
      let source := s!"set_option {name} {val} in\ndef value : Nat := 0"
      let entries ← SourceAudit.parse env source owner.toString
      let result := SourceAudit.auditRegCommands owner entries
      assertTest s!"input.option.{label}.{name}" (if accepted then result.isOk else
        match result with
        | .error e => e == s!"contract.reg:option_literal_type:{owner}:{name}"
        | .ok _ => false)
  for name in #["debug.skipKernelTC", "compiler.extract_closed", "maxRecDepth.extra",
      "backward.isDefEq.respectTransparency.extra", "pp.universes"] do
    for (wrapper, wrap) in wrappers do
      let entries ← SourceAudit.parse env
        (wrap s!"set_option {name} true in\ndef value : Nat := 0") owner.toString
      let result := SourceAudit.auditRegCommands owner entries
      assertTest s!"input.option.name.{wrapper}.{name}" (match result with
        | .error e => e == s!"contract.reg:option_not_allowed:{owner}:{name}"
        | .ok _ => false)
  for modifier in #["unsafe", "partial"] do
    for (kind, decl) in #[("def", "def value : Nat := 0"),
        ("theorem", "theorem value : True := by trivial"),
        ("opaque", "opaque value : Nat := 0"),
        ("instance", "instance value : Inhabited Nat := ⟨0⟩"),
        ("structure", "structure Value where\n  value : Nat"),
        ("example", "example : True := by trivial")] do
      for (wrapper, wrap) in wrappers do
        let entries ← SourceAudit.parse env (wrap (modifier ++ " " ++ decl)) owner.toString
        let result := SourceAudit.auditRegCommands owner entries
        assertTest s!"input.modifier.{modifier}.{kind}.{wrapper}" (match result with
          | .error e => e == s!"contract.reg:declaration_modifier_not_allowed:{owner}:{modifier}"
          | .ok _ => false)
        let restored ← SourceAudit.parse env (wrap decl) owner.toString
        assertTest s!"input.modifier.restore.{modifier}.{kind}.{wrapper}"
          (SourceAudit.auditRegCommands owner restored).isOk
  for source in #["noncomputable def value : Nat := 0", "private def value : Nat := 0",
      "protected def value : Nat := 0", "def value : Nat := by exact 0",
      "def value : Nat := set_option maxRecDepth 4096 in 0",
      "theorem value : True := by set_option maxHeartbeats 200000 in trivial"] do
    let entries ← SourceAudit.parse env source owner.toString
    assertTest s!"input.positive.{source}" (SourceAudit.auditRegCommands owner entries).isOk
  for (label, source) in #[
      ("term", "def value : Nat := set_option debug.skipKernelTC true in 0"),
      ("tactic", "theorem value : True := by set_option debug.skipKernelTC true in trivial")] do
    let entries ← SourceAudit.parse env source owner.toString
    assertTest s!"input.option.nested.{label}" (match SourceAudit.auditRegCommands owner entries with
      | .error e => e == s!"contract.reg:option_not_allowed:{owner}:debug.skipKernelTC"
      | .ok _ => false)
  for (label, source, key) in #[
      ("in", "open Nat in\ndef value : Nat := 0", ``Parser.Command.openSimple),
      ("option", "set_option maxRecDepth 4096 in\ndef value : Nat := 0", ``Parser.Command.set_option),
      ("mutual", "mutual\ndef a : Nat := 0\ndef b : Nat := 1\nend", ``Parser.Command.mutual)] do
    let entries ← SourceAudit.parse env source owner.toString
    assertTest s!"input.origin.{label}"
      (SourceAudit.hasAuthoredElaboration entries (NameSet.empty.insert key))
  let entries ← SourceAudit.parse env "def value : Nat := 0" owner.toString
  let some original := entries[0]? | throwError "control:declaration_missing"
  for kind in #[``Parser.Command.in, ``Parser.Command.mutual, ``Parser.Command.set_option,
      `Unrecognized.commandWrapper] do
    let malformed := entries.map fun e =>
      { e with originCommand := mkNode kind #[mkAtom "wrapper"] }
    assertTest s!"input.wrapper.{kind}" (match SourceAudit.auditRegCommands owner malformed with
      | .error e => e.startsWith "contract.reg:wrapper_not_allowed:" ||
          e.startsWith "contract.reg:metaprogramming_not_allowed:"
      | .ok _ => false)
  for (label, source, child, replacement) in #[
      ("in_separator", "open Nat in\ndef value : Nat := 0", 1, mkAtom "while"),
      ("option_suffix", "set_option maxRecDepth 4096", 2, mkNode `null #[mkAtom "."]),
      ("mutual_children", "mutual\ndef value : Nat := 0\nend", 1,
        mkNode `Unrecognized.children #[original.command])] do
    let parsed ← SourceAudit.parse env source owner.toString
    let some parsedEntry := parsed[0]? | throwError "control:wrapper_missing"
    let origin := parsedEntry.originCommand.setArg child replacement
    let malformed := entries.map fun e => { e with originCommand := origin }
    assertTest s!"input.wrapper.{label}" (match SourceAudit.auditRegCommands owner malformed with
      | .error e => e.startsWith "contract.reg:wrapper_not_allowed:"
      | .ok _ => false)
end LeanInformationAuditRegTests.ContractInputLimits
