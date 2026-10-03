import LeanInformationAuditInterface.Store

namespace LeanInformationAudit.RegMigration

open Lean

private def optionJson (options : Options) : Json :=
  Json.str (repr options)

private def optionExprJson (value : Option Expr) : Json :=
  match value with
  | none => Json.null
  | some expression => Json.str expression.toString

private def registrationJson (owner : Name) (input : RegistrationInput) : Json :=
  let entry := input.entry
  Json.mkObj [
    ("owner", Json.str owner.toString),
    ("source_text", Json.str input.sourceText),
    ("options", optionJson input.options),
    ("theorem", Json.str entry.theoremName.toString),
    ("unit", Json.str entry.unitName.toString),
    ("arena", Json.str entry.arenaName.toString),
    ("realization", Json.str entry.realizationName.toString),
    ("variation", Json.str entry.variationWitness.toString),
    ("sensitivity", Json.str entry.sensitivityWitness.toString),
    ("catalog", Json.str entry.catalogId.toString),
    ("object_arena", Json.str entry.objectArenaName.toString),
    ("resolved_arena", Json.str entry.resolvedArenaName.toString),
    ("registration_module", Json.str entry.registrationModuleName.toString),
    ("statement_identity", Json.str entry.statementIdentity),
    ("source_bound", Json.bool entry.sourceBound),
    ("local_registration_names", Json.bool entry.localRegistrationNames),
    ("supplied_primitives", optionExprJson input.suppliedPrimitives),
    ("via_descriptor", optionExprJson input.viaDescriptor),
    ("output_evidence", optionExprJson input.outputEvidence),
    ("realization_source", Json.str (input.realizationSource.map Name.toString |>.getD ""))]

private def enrollmentJson (owner : Name) (input : TemplateEnrollmentInput) : Json :=
  Json.mkObj [
    ("owner", Json.str owner.toString),
    ("name", Json.str input.name.toString),
    ("version", Json.num input.version),
    ("constructors", Json.arr (input.constructors.map fun name => Json.str name.toString)),
    ("source_text", Json.str input.sourceText),
    ("options", optionJson input.options)]

private def sealJson (owner : Name) (input : SealInput) : Json :=
  Json.mkObj [
    ("owner", Json.str owner.toString),
    ("root_id", Json.str input.rootId.toString),
    ("options", optionJson input.options)]

private def occurrenceJson (entry : ExpectedOccurrence) : Json :=
  Json.mkObj [
    ("root_id", Json.str entry.rootId.toString),
    ("object_arena", Json.str entry.objectArenaName.toString),
    ("theorem", Json.str entry.theoremName.toString),
    ("statement_identity", Json.str entry.statementIdentity),
    ("registration_module", Json.str entry.registrationModuleName.toString),
    ("captured_statement", optionExprJson entry.capturedStatement)]

private def rootJson (owner : Name) (entry : RootCatalogContract) : Json :=
  Json.mkObj [
    ("owner", Json.str owner.toString),
    ("root_id", Json.str entry.rootId.toString),
    ("expected", Json.arr (entry.expected.map occurrenceJson)),
    ("source", Json.arr (entry.source.map occurrenceJson)),
    ("baseline", Json.arr (entry.baseline.map occurrenceJson)),
    ("companion_prefix", Json.str (entry.companionPrefix.map Name.toString |>.getD ""))]

private def extract (env : Environment) : Json :=
  Json.mkObj [
    ("schema", Json.str "reg-migration-inputs-v1"),
    ("registrations", Json.arr ((RegistrationInputs.owned env).map (fun (owner, input) => registrationJson owner input))),
    ("templates", Json.arr ((TemplateEnrollmentInputs.owned env).map (fun (owner, input) => enrollmentJson owner input))),
    ("seals", Json.arr ((SealInputs.owned env).map (fun (owner, input) => sealJson owner input))),
    ("roots", Json.arr ((RootCatalogs.owned env).map (fun (owner, input) => rootJson owner input))),
    ("expected", Json.arr ((ExpectedOccurrenceManifest.owned env).map (fun (_, input) => occurrenceJson input)))]

syntax (name := regMigrationExtract) "#reg_migration_extract " str : command

elab_rules : command
  | `( #reg_migration_extract $path:str ) =>
    let output := extract (← getEnv)
    liftIO <| IO.FS.writeFile path.getString (output.compress ++ "\n")

end LeanInformationAudit.RegMigration

