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
  for theoremName in [`first, `second] do
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
''')
        (package / 'Reader.lean').write_text('''import Writer
open Lean LeanInformationAudit LeanInformationAudit.TemplateBinding

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Writer }] {} (loadExts := true)
  let env := env.setMainModule `Reader
  let check (label : String) (ok : Bool) :=
    unless ok do throw <| IO.userError s!"[FAIL] {label}"
  check "imported_inventory" ((inventory env).map (·.key.theoremName) == #[`first, `second])
  check "imported_claims" ((claims env).map (·.key.theoremName) == #[`first, `second])
  check "event_origins" ((ownedEvents env).map (·.1) == #[`Writer, `Writer])
  check "claim_origins" ((ownedClaims env).map (·.1) == #[`Writer, `Writer])
  check "claimed_owner_is_not_origin" ((claims env).all (·.owner == `assertedOwner))
  let event := (inventory env)[0]!
  let claim := (claims env)[0]!
  let localEnv := addClaim (addOccurrence env event) claim
  check "local_event_origin" ((ownedEvents localEnv).back?.map (·.1) == some `Reader)
  check "local_claim_origin" ((ownedClaims localEnv).back?.map (·.1) == some `Reader)
''')
        with (package / 'lakefile.toml').open('a') as config:
            # The reader loads Writer's initializers through the interpreter; on Linux that needs exported symbols.
            config.write('\n[[lean_lib]]\nname = "Writer"\n[[lean_exe]]\nname = "reader"\nroot = "Reader"\n'
                         'supportInterpreter = true\n')
        result = self.guarded_command([self.lake, 'build', 'Writer', 'reader'], cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        print('INTERFACE_STORE_BUILD compile_errors=0 exit_code=0', flush=True)
        result = self.guarded_command([self.lake, 'env', str(package / '.lake/build/bin/reader')],
                                      cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
