import LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural
import InformationSourceFixture

namespace LeanInformationAudit.Tests.DeclaredIndependentSources
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape
open DeclaredStructural (template)

abbrev arena : StructuralArena := ⟨Int⟩
def signature : StructuralPrimitiveSignature := ⟨Unit, inferInstance, fun _ => Nat⟩
def law : StructuralPrimitiveLawArena arena where
  signature := signature
  Law r := ∀ x : Int, r.readout () x = Int.natAbs x

structural_theorem independentSource in law
  readout via (template arena signature (fun _ => Int.natAbs))
  realization (template arena signature (fun _ => Int.natAbs)) := by
    intro x
    rfl

abbrev fixtureArena : StructuralArena := ⟨Option Int⟩
def fixtureSignature : StructuralPrimitiveSignature := ⟨Unit, inferInstance, fun _ => Bool⟩
def fixtureLaw : StructuralPrimitiveLawArena fixtureArena where
  signature := fixtureSignature
  Law r := ∀ x : Option Int, r.readout () x = InformationSourceFixture.compositeReadout x

structural_theorem judgePackageSource in fixtureLaw
  readout via (template fixtureArena fixtureSignature
    (fun _ => InformationSourceFixture.compositeReadout))
  realization (template fixtureArena fixtureSignature
    (fun _ => InformationSourceFixture.compositeReadout)) := by
    intro x
    rfl

run_meta do
  let some record := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``independentSource)
    | throwError "setup: missing independent source binding"
  let .declaredValidated certificate := record.result
    | throwError "[FAIL] independent_composite_source_binding_validated result={repr record.result}"
  logInfo "[PASS] independent_standard_source_binding_validated"
  let some source := certificate.argumentInputs.find?
      (·.name == ``Int.natAbs)
    | throwError "[FAIL] independent_source_binding_retains_native_identities"
  unless source.typeIdentity.length == 64 &&
      source.bodyIdentity.length == 64 do
    throwError "[FAIL] independent_source_binding_retains_native_identities"
  logInfo "[PASS] independent_source_binding_retains_native_identities"
  let some fixture := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``judgePackageSource)
    | throwError "setup: missing judge package source binding"
  unless fixture.result matches .declaredUnresolved _ do
    throwError "[FAIL] judge_package_source_rejected"
  logInfo "[PASS] judge_package_source_rejected"

end LeanInformationAudit.Tests.DeclaredIndependentSources
