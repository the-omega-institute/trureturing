import LeanInformationAudit.Registry.Evidence
import LeanInformationAuditAnalysis.Tests.AllowlistSources

open Lean Meta LeanInformationAudit LeanInformationAudit.TemplateAudit

-- The constructor occurs only in the Interface-owned default's data body.
def interfaceDefaultClaim : Prop :=
  ∃ value : EscapeRecordInput, value = TemplateBindingClaim.escapeInput._default

def foreignBodyClaim : Prop := ImportedAllowlistSources.proofRead () true = true

namespace UnrelatedDeclarationNames
def payload : Nat := 37
def support : Nat := payload
def claim : Prop := support = 37
theorem proofLeaf : claim := rfl
def proofCarrier : Subtype fun n : Nat => n = 37 := ⟨37, proofLeaf⟩
def proofClaim : Prop := proofCarrier.val = 37
end UnrelatedDeclarationNames

private def dependencies (statement : Name) : MetaM (Array Name) := do
  let event : TemplateOccurrenceEvent := {
    key := default, unitName := ``True.intro, realizationName := ``True.intro,
    statement := mkConst statement, levelParams := [], statementIdentity := "fixture",
    arena := mkConst ``Bool, registrationSource := "fixture",
    registrationSourceIdentity := "fixture" }
  inspectionDependencies event

run_meta do
  let env ← getEnv
  unless (RegistrationReifier.declaringModuleOf env
      ``TemplateBindingClaim.escapeInput._default) == some `LeanInformationAuditInterface.Records do
    throwError "[FAIL] interface_default_compiler_owner"
  let names ← dependencies ``interfaceDefaultClaim
  unless names.contains ``EscapeRecordInput.mk do
    throwError "[FAIL] interface_default_body_dependency"
  logInfo "[PASS] interface_default_body_dependency"

run_meta do
  let names ← dependencies ``foreignBodyClaim
  unless names.contains ``ImportedAllowlistSources.proofRead do
    throwError "[FAIL] foreign_type_boundary_missing"
  if names.any (fun name => (privateToUserName name) == `ImportedAllowlistSources.relay) then
    throwError "[FAIL] foreign_body_unfolded"
  logInfo "[PASS] foreign_body_opaque"

-- Local declarations have no imported-module index. Exercise that compiler
-- fallback with a Reg main module and with an unrelated main module; imported
-- Interface/foreign owners above remain their actual compiler source modules.
run_meta do
  let env ← getEnv
  unless (env.getModuleIdxFor? ``UnrelatedDeclarationNames.support).isNone do
    throwError "[FAIL] local_compiler_owner"
  for (owner, expected) in #[(`Reg.Support.OwnerProbe, true), (`Unrelated.OwnerProbe, false)] do
    withEnv (env.setMainModule owner) do
      let names ← dependencies ``UnrelatedDeclarationNames.claim
      unless names.contains ``UnrelatedDeclarationNames.payload == expected do
        throwError "[FAIL] local_data_owner_{owner}"
      logInfo m!"[PASS] local_data_owner_{owner}"
  let names ← dependencies ``UnrelatedDeclarationNames.proofClaim
  if names.contains ``UnrelatedDeclarationNames.proofLeaf then
    throwError "[FAIL] proof_implementation_retained"
  logInfo "[PASS] proof_implementation_erased"
