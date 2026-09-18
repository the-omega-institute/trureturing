import LeanInformationAudit.Syntax
import LeanInformationAudit.Tests.RegistrationGates.Positive
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

namespace LeanInformationAudit.Tests.DeclaredKeywords
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

local instance : DecidableEq RegistrationPositive.arena.State := instDecidableEqBool

/-- Parse the actual source spelling at runtime so a reserved-token mutation
reports a named test failure, rather than preventing this oracle from compiling. -/
elab "observe_declared_keywords" : command => do
  let initial ← get
  let mut identifiers := true
  for source in #["theorem sensitivity : True := True.intro",
      "def variation : Bool := true", "def via : Nat := Nat.zero",
      "def escape : Bool := true", "def continues : Nat := Nat.zero", "def from : Bool := false"] do
    match Parser.runParserCategory (← getEnv) `command source with
    | .error _ => identifiers := false
    | .ok command =>
      try elabCommand command catch _ => identifiers := false
  let saved ← get
  let commands := #[
    "register_information_template cutRealization",
    "theorem keywordSource : RegistrationPositive.arena.Law RegistrationPositive.good := rfl",
    "theorem keywordBridge : LegacyPrimitiveRealization RegistrationPositive.arena " ++
      "(RegistrationPositive.arena.Law RegistrationPositive.good) RegistrationPositive.good := RegistrationPositive.bridge",
    "register_information_theorem keywordSource in RegistrationPositive.arena " ++
      "readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)) " ++
      "primitives RegistrationPositive.good.toPrimitiveBundle realization keywordBridge " ++
      "variation RegistrationPositive.lawVariation sensitivity RegistrationPositive.slotSensitivity"]
  let mut grammar := true
  for source in commands do
    match Parser.runParserCategory (← getEnv) `command source with
    | .error error => grammar := false; logInfo error
    | .ok command =>
      try elabCommand command catch error => grammar := false; logInfo error.toMessageData
  let theoremName := (← getCurrNamespace).str "keywordSource"
  let entry := InformationRegistry.find? (← getEnv) theoremName
  grammar := grammar && entry.isSome && !(← get).messages.hasErrors
  let diagnostics ← (← get).messages.toList.mapM fun m => m.data.toString
  set saved
  set initial
  if !grammar then for diagnostic in diagnostics do logInfo diagnostic
  for (label, ok) in #[("keywords_identifiers", identifiers), ("keywords_registration", grammar)] do
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

observe_declared_keywords

end LeanInformationAudit.Tests.DeclaredKeywords
