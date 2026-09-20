"""Stable declaration ownership and import persistence without the judge."""
import re

from test_native_support import ROOT


class NativeRecordTests:
    def test_interface_records_have_single_owner(self):
        interface = ROOT / 'tools/lean-inspector-interface/LeanInformationAuditInterface/Records.lean'
        self.assertTrue(interface.is_file(), 'missing Interface record owner')
        declarations = r'(?m)^(?:structure|inductive|abbrev)\s+(\w+)\b'
        moved = set(re.findall(declarations, interface.read_text()))
        self.assertIn('TemplateOccurrenceEvent', moved)
        self.assertIn('TemplateBindingClaim', moved)
        self.assertTrue({'DependencyIdentity', 'TemplateBindingCertificate',
                         'TemplateBindingResult', 'BindingRecord'} <= moved)
        implementation = ROOT / 'tools/lean-inspector/LeanInformationAudit'
        for path in implementation.rglob('*.lean'):
            if 'Tests' in path.parts:
                continue
            duplicates = moved & set(re.findall(declarations, path.read_text()))
            self.assertFalse(duplicates, f'[FAIL] {path}: duplicate Interface types: {duplicates}')

    def test_interface_store_cross_module_persistence(self):
        package, env = self.interface_package()
        (package / 'Writer.lean').write_text('''import LeanInformationAuditInterface.Store
open Lean LeanInformationAudit LeanInformationAudit.TemplateBinding

run_cmd do
  for theoremName in [`first, `second, `third] do
    let key : TemplateOccurrenceKey := {
      root := `root, registrationModule := `assertedOwner,
      theoremName, objectArena := `arena, catalog := `catalog }
    let event : TemplateOccurrenceEvent := {
      key, unitName := `unit, realizationName := `realization,
      statement := mkConst ``True, levelParams := [], statementIdentity := "statement",
      arena := mkConst ``Bool, registrationSource := "source", registrationSourceIdentity := "identity" }
    let claim : TemplateBindingClaim := {
      key, arena := event.arena, descriptor := none, owner := `assertedOwner }
    modifyEnv fun env => addClaim (addOccurrence env event) claim
    let dependency : TemplateAudit.DependencyIdentity := {
      name := `input, owner := `inputOwner, typeIdentity := "type", bodyIdentity := "body" }
    let certificate : TemplateBindingCertificate := {
      evidenceRef := "evidence", key, planIdentity := "plan", descriptorIdentity := "descriptor",
      actualIdentity := "actual", argumentInputs := #[dependency], extractionInputs := #[dependency] }
    let result := if theoremName == `first then .undeclared
      else if theoremName == `second then .declaredUnresolved "diagnostic"
      else TemplateBindingResult.declaredValidated certificate
    -- Transport retains the asserted result; this fixture performs no assessment.
    modifyEnv fun env => addRecord env {
      occurrence := event, descriptor := none, bindingOwner := none, result }
''')
        (package / 'Overlay.lean').write_text('''import Writer
open Lean LeanInformationAudit LeanInformationAudit.TemplateBinding

run_cmd do
  let record := (records (← getEnv))[0]!
  for theoremName in [`fourth, `fifth] do
    modifyEnv fun env => addRecord env { record with
      occurrence := { record.occurrence with key := { record.occurrence.key with theoremName } },
      bindingOwner := some `assertedOverlay }
''')
        (package / 'Reader.lean').write_text('''import Overlay
open Lean LeanInformationAudit LeanInformationAudit.TemplateBinding

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Overlay }] {} (loadExts := true)
  let env := env.setMainModule `Reader
  let check (label : String) (ok : Bool) :=
    unless ok do throw <| IO.userError s!"[FAIL] {label}"
  check "no_implementation_import" (!env.header.moduleNames.any
    (fun name => (`LeanInformationAudit).isPrefixOf name))
  for name in #[``TemplateAudit.DependencyIdentity, ``TemplateBindingCertificate,
      ``TemplateBindingResult, ``BindingRecord, ``BindingRecord.mk, ``BindingRecord.result] do
    check s!"record_owner:{name}" ((env.getModuleIdxFor? name).map
      (env.allImportedModuleNames[·.toNat]!) == some `LeanInformationAuditInterface.Records)
  for name in #[``records, ``addRecord, ``importedRecords, ``ownedRecords,
      `LeanInformationAudit.TemplateBinding.bindingRecords,
      `LeanInformationAudit.TemplateBinding.bindingClaims,
      `LeanInformationAudit.TemplateBinding.occurrenceInventory] do
    let some (actual, _) := env.constants.toList.find? (fun (actual, _) =>
        privateToUserName actual == name)
      | throw <| IO.userError s!"[FAIL] missing_store_constant:{name}"
    check s!"store_owner:{name}" ((env.getModuleIdxFor? actual).map
      (env.allImportedModuleNames[·.toNat]!) == some `LeanInformationAuditInterface.Store)
  check "imported_inventory" ((inventory env).map (·.key.theoremName) == #[`first, `second, `third])
  check "imported_claims" ((claims env).map (·.key.theoremName) == #[`first, `second, `third])
  check "event_origins" ((ownedEvents env).map (·.1) == #[`Writer, `Writer, `Writer])
  check "claim_origins" ((ownedClaims env).map (·.1) == #[`Writer, `Writer, `Writer])
  check "claimed_owner_is_not_origin" ((claims env).all (·.owner == `assertedOwner))
  let expected := #[`first, `second, `third, `fourth, `fifth]
  check "imported_records" ((records env).map (·.occurrence.key.theoremName) == expected)
  check "record_origins" ((ownedRecords env).map (·.1) ==
    #[`Writer, `Writer, `Writer, `Overlay, `Overlay])
  check "owned_record_order" ((ownedRecords env).map (·.2.occurrence.key.theoremName) == expected)
  check "record_defaults" ((records env).all (fun record =>
    record.schemaVersion == 1 && record.compatibilityVersion == 7 && record.escape == {}))
  check "undeclared_result" ((records env)[0]!.result matches .undeclared)
  check "unresolved_result" ((records env)[1]!.result matches .declaredUnresolved "diagnostic")
  let .declaredValidated certificate := (records env)[2]!.result
    | throw <| IO.userError "[FAIL] stored_certificate_shape"
  check "certificate_fields" (certificate.evidenceRef == "evidence" &&
    certificate.key.theoremName == `third && certificate.planIdentity == "plan" &&
    certificate.descriptorIdentity == "descriptor" && certificate.actualIdentity == "actual" &&
    certificate.escape == {})
  for dependencies in #[certificate.argumentInputs, certificate.extractionInputs] do
    check "dependency_fields" (dependencies.size == 1 && dependencies.all (fun dependency =>
      dependency.name == `input && dependency.owner == `inputOwner &&
      dependency.typeIdentity == "type" && dependency.bodyIdentity == "body"))
  check "overlay_assertion_is_not_origin" ((records env)[4]!.bindingOwner == some `assertedOverlay)
  let event := (inventory env)[0]!
  let claim := (claims env)[0]!
  let localEnv := addClaim (addOccurrence env event) claim
  check "local_event_origin" ((ownedEvents localEnv).back?.map (·.1) == some `Reader)
  check "local_claim_origin" ((ownedClaims localEnv).back?.map (·.1) == some `Reader)
  let mut localEnv := localEnv
  for theoremName in [`sixth, `seventh] do
    localEnv := addRecord localEnv { (records env)[0]! with
      occurrence := { event with key := { event.key with theoremName } } }
  let expected := expected ++ #[`sixth, `seventh]
  check "local_record_order" ((records localEnv).map (·.occurrence.key.theoremName) == expected)
  check "local_owned_record_order" ((ownedRecords localEnv).map
    (·.2.occurrence.key.theoremName) == expected)
  check "imported_records_exclude_locals" ((importedRecords localEnv).map
    (·.2.occurrence.key.theoremName) == #[`first, `second, `third, `fourth, `fifth])
  check "local_record_origins" ((ownedRecords localEnv).map (·.1) ==
    #[`Writer, `Writer, `Writer, `Overlay, `Overlay, `Reader, `Reader])
  IO.println "[PASS] Interface-only record reader, compiler owners, imported/local origins and order"
''')
        with (package / 'lakefile.toml').open('a') as config:
            # The reader loads Writer's initializers through the interpreter; on Linux that needs exported symbols.
            config.write('\n[[lean_lib]]\nname = "Writer"\n[[lean_lib]]\nname = "Overlay"\n'
                         '[[lean_exe]]\nname = "reader"\nroot = "Reader"\n'
                         'supportInterpreter = true\n')
        result = self.guarded_command([self.lake, 'build', 'Overlay', 'reader'], cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        print('INTERFACE_STORE_BUILD compile_errors=0 exit_code=0', flush=True)
        result = self.guarded_command([self.lake, 'env', str(package / '.lake/build/bin/reader')],
                                      cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_interface_edit_rebuilds_implementation_consumer(self):
        self.reg_package()
        self.run_lake('build', 'Fixture')
        # Use the real plan decoder: its DependencyIdentity construction must
        # be re-elaborated when the Interface's field type changes.
        implementation = 'LeanInformationAudit/RegistryTypes.lean'
        self.write(implementation, (ROOT / 'tools/lean-inspector' / implementation).read_text())
        self.write('Reg/Support/Entry.lean',
                   'import D5.A\nimport LeanInformationAudit.RegistryTypes\n')
        self.make_lean('Reg.Support.Entry')
        content = self.root / '.lake/build/lib/lean/D5/A.olean'
        before = (content.stat().st_mtime_ns, content.read_bytes())
        interface = self.root / 'tools/lean-inspector-interface/LeanInformationAuditInterface/Records.lean'
        original = interface.read_text()
        prefix, dependency = original.split('structure DependencyIdentity where\n', 1)
        fields, rest = dependency.split('  deriving Inhabited', 1)
        self.assertIn('  typeIdentity : String\n', fields)
        interface.write_text(prefix + 'structure DependencyIdentity where\n' +
                             fields.replace('  typeIdentity : String\n', '  typeIdentity : Nat\n') +
                             '  deriving Inhabited' + rest)
        failed = self.make_lean('Reg.Support.Entry', success=False)
        self.assertIn('RegistryTypes.lean', failed.stdout + failed.stderr)
        self.assertIn('typeIdentity', failed.stdout + failed.stderr)
        self.assertEqual((content.stat().st_mtime_ns, content.read_bytes()), before)
        interface.write_text(original)
        self.make_lean('Reg.Support.Entry')
        self.assertEqual((content.stat().st_mtime_ns, content.read_bytes()), before)
