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
open Lean LeanInformationAudit
run_cmd do
  for theoremName in [`first, `second, `third] do
    modifyEnv fun env => RegistrationInputs.add env {
      entry := { theoremName, arenaName := `arena, unitName := `unit,
                 realizationName := `realization, registrationModuleName := `assertedOwner }
      sourceText := "original source", options := maxRecDepth.set {} 731
      suppliedPrimitives := some (mkConst ``Bool.true)
      declaration := some { theoremName, arena := `arena,
                            descriptor := some (mkConst ``Nat),
                            escapeInput := { openContinuation := true } } }
  modifyEnv fun env => TemplateEnrollmentInputs.add env {
    owner := `assertedOwner, name := `template, version := 1, constructors := #[`AST],
    sourceText := "original enrollment", options := {} }
  modifyEnv fun env => SealInputs.add env { rootId := `assertedOwner, options := {} }
''')
        (package / 'Overlay.lean').write_text('''import Writer
open Lean LeanInformationAudit
run_cmd do
  let some (_, input) := (RegistrationInputs.owned (← getEnv))[0]? | throwError "missing input"
  for theoremName in [`fourth, `fifth] do
    modifyEnv fun env => RegistrationInputs.add env {
      input with entry := { input.entry with theoremName } }
''')
        (package / 'Reader.lean').write_text('''import Overlay
open Lean LeanInformationAudit
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Overlay }] {} (loadExts := true)
  let env := env.setMainModule `Reader
  let check (label : String) (ok : Bool) :=
    unless ok do throw <| IO.userError s!"[FAIL] {label}"
  check "no_implementation_import" (!env.header.moduleNames.any
    (fun name => (`LeanInformationAudit).isPrefixOf name))
  let rows := RegistrationInputs.owned env
  let names := #[`first, `second, `third, `fourth, `fifth]
  check "imported_input_order" (rows.map (·.2.entry.theoremName) == names)
  check "native_container_owners" (rows.map (·.1) ==
    #[`Writer, `Writer, `Writer, `Overlay, `Overlay])
  check "claimed_owner_is_not_origin" (rows.all (·.2.entry.registrationModuleName == `assertedOwner))
  check "author_scope_retained" (rows.all fun (_, input) =>
    input.sourceText == "original source" && maxRecDepth.get input.options == 731 &&
    input.suppliedPrimitives.any (·.isConstOf ``Bool.true) &&
    input.entry.derivedCertificate.isNone &&
    input.declaration.any (fun declaration => declaration.arena == `arena &&
      declaration.descriptor.any (·.isConstOf ``Nat) && declaration.escapeInput.openContinuation))
  let enrollments := TemplateEnrollmentInputs.owned env
  check "enrollment_inputs" (match enrollments with
    | #[(owner, enrollment)] => owner == `Writer && enrollment.owner == `assertedOwner &&
        enrollment.name == `template && enrollment.constructors == #[`AST] && enrollment.version == 1
    | _ => false)
  let seals := SealInputs.owned env
  check "seal_inputs" (match seals with
    | #[(owner, sealInput)] => owner == `Writer && sealInput.rootId == `assertedOwner
    | _ => false)
  for name in #[``RegistrationInputs.owned, ``RegistrationInputs.add,
      ``TemplateEnrollmentInputs.owned, ``SealInputs.owned] do
    check s!"store_owner:{name}" ((env.getModuleIdxFor? name).map
      (env.allImportedModuleNames[·.toNat]!) == some `LeanInformationAuditInterface.Store)
  for name in #[`LeanInformationAudit.TemplateBinding.bindingRecords,
      `LeanInformationAudit.TemplateBinding.occurrenceInventory,
      `LeanInformationAudit.TemplateBinding.bindingClaims] do
    check s!"no_persisted_verdict:{name}" (!env.constants.toList.any
      (fun (actual, _) => privateToUserName actual == name))
  let some (_, first) := rows[0]? | throw <| IO.userError "[FAIL] imported_input_absent"
  let mut localEnv := env
  for theoremName in [`sixth, `seventh] do
    let input := first
    localEnv := RegistrationInputs.add localEnv {
      input with entry := { input.entry with theoremName } }
  let locals := RegistrationInputs.owned localEnv
  check "local_order" (locals.map (·.2.entry.theoremName) == names ++ #[`sixth, `seventh])
  check "local_owners" (locals.map (·.1) ==
    #[`Writer, `Writer, `Writer, `Overlay, `Overlay, `Reader, `Reader])
  IO.println "[PASS] Interface raw inputs, native owners, author scope and import/local order"
''')
        with (package / 'lakefile.toml').open('a') as config:
            config.write('\n[[lean_lib]]\nname = "Writer"\n[[lean_lib]]\nname = "Overlay"\n'
                         '[[lean_exe]]\nname = "reader"\nroot = "Reader"\n'
                         'supportInterpreter = true\n')
        result = self.guarded_command([self.lake, 'build', 'Overlay', 'reader'], cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        print('INTERFACE_STORE_BUILD compile_errors=0 exit_code=0', flush=True)
        result = self.guarded_command([self.lake, 'env', str(package / '.lake/build/bin/reader')],
                                      cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

class NativeInterfaceConsumerTests:
    def test_interface_edit_rebuilds_implementation_consumer(self):
        self.reg_package()
        self.run_lake('build', 'Fixture')
        # A module reading the real Interface dependency identity must re-elaborate
        # when that field type changes; D5 content does not rebuild. Reg is the
        # fixture's Interface consumer (Impl consumers depend on it the same way).
        self.write('Reg/Support/Entry.lean', 'import D5.A\nimport LeanInformationAuditInterface.Records\n'
                   'def dependencyType (d : LeanInformationAudit.TemplateAudit.DependencyIdentity) : String :=\n'
                   '  d.typeIdentity\n')
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
        self.assertIn('Reg/Support/Entry.lean', failed.stdout + failed.stderr)
        self.assertIn('typeIdentity', failed.stdout + failed.stderr)
        self.assertEqual((content.stat().st_mtime_ns, content.read_bytes()), before)
        interface.write_text(original)
        self.make_lean('Reg.Support.Entry')
        self.assertEqual((content.stat().st_mtime_ns, content.read_bytes()), before)
