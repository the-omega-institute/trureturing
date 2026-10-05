"""Legacy recorder declarations build with only the installed core toolchain."""
import json
import os
import re
import shutil
import tomllib

from test_native_support import ROOT, publication, copy_contract_interface


class NativeInterfaceTests:
    def test_output_audit_follows_compiler_package_owners(self):
        package, env = self.interface_package()
        for relative in ('Projection/OutputOnlyAudit.lean', 'Registry/Repository.lean'):
            source = ROOT / 'tools/lean-inspector/LeanInformationAudit' / relative
            target = package / 'LeanInformationAudit' / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
        for relative in ('BindingRecords.lean', 'EscapeEvidence.lean', 'RuntimeInputs.lean',
                         'InputTypes.lean', 'SnapshotTypes.lean', 'SourceSelection.lean', 'OutputSyntax.lean'):
            source = ROOT / 'tools/lean-inspector/LeanInformationAudit' / relative
            target = package / 'LeanInformationAudit' / relative
            shutil.copyfile(source, target)
        # This core-only audit fixture needs the real capability type, but does
        # not execute catalog construction. Copy its exact declaration; private
        # construction and all field types stay identical to the producer.
        catalog = (ROOT / 'tools/lean-inspector/LeanInformationAudit/CatalogBuilder.lean').read_text()
        start = catalog.index('structure ValidatedSourceSnapshot where\n')
        stop = catalog.index('\ndef ValidatedSourceSnapshot.sourceEntries', start)
        (package / 'LeanInformationAudit/CatalogBuilder.lean').write_text(
            'import LeanInformationAudit.BindingRecords\n'
            'import LeanInformationAudit.Registry.Repository\n'
            'namespace LeanInformationAudit\nopen Lean\n' +
            catalog[start:stop] + '\nend LeanInformationAudit\n')
        # Illegal capabilities exist only in disposable fixtures. Names deliberately
        # disagree with owners, including a foreign package impersonating the judge.
        owners = [('LeanInformationAuditInterface', 'OutsideJudgeNamespace'),
                  ('LeanInformationAudit', 'ImplProbe'), ('Reg', 'RegProbe'),
                  ('D5', 'ContentProbe'), ('LeanInformationAuditForeign', 'LeanInformationAudit.Impostor')]
        for owner, namespace in owners:
            target = package / owner / 'OwnerProbe.lean'
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(f'''import Lean
open Lean Elab Command
namespace {namespace}
def read : CommandElabM Unit := do
  let _ ← liftIO <| IO.FS.readFile "never-executed"
def reference : CommandElabM Unit := do
  let _ ← getRef
def loader : CommandElabM Unit := do
  let _ ← liftIO <| Lean.findOLean `Lean
def mutate : CommandElabM Unit := do setEnv (← getEnv)
def clean : CommandElabM Unit := pure ()
end {namespace}
''')
        probe = package / 'LeanInformationAudit/OwnerConsumer.lean'
        imports = ''.join(f'import {owner}.OwnerProbe\n' for owner, _ in owners)
        declarations, checks = [], []
        for index, (owner, namespace) in enumerate(owners):
            for action, capability in [('read', 'IO.FS.readFile'),
                                       ('reference', 'Lean.MonadRef.getRef'),
                                       ('loader', 'Lean.findOLean'), ('mutate', 'Lean.setEnv'),
                                       ('clean', None)]:
                stem = f'probe{index}_{action}'
                declarations.append(f'''def {stem}Publication (_ : ValidatedSourceSnapshot) (_ : SealInput) : CommandElabM Unit := {namespace}.{action}
def {stem}Seal : ValidatedSourceSnapshot → SealInput → CommandElab := terminalSealCommand {stem}Publication
def {stem}StageBody (_ : Name) : CommandElabM Unit := {namespace}.{action}
def {stem}Stage : CommandElab := terminalInformationAnalysisStageCommand {stem}StageBody
def {stem}ExportBody (_ : Name) (_ : List ArtifactKind) : CommandElabM AnalysisExportPlan := do
  {namespace}.{action}
  return {{ artifacts := [] }}
def {stem}Export : CommandElab := terminalInformationAnalysisExportCommand {stem}ExportBody
''')
                for mode, audit in [('Seal', 'auditSealOutputOnly'),
                                    ('Stage', 'auditInformationAnalysisStage'),
                                    ('Export', 'auditInformationAnalysisExport')]:
                    reject = index < 2 and capability is not None and (action != 'mutate' or mode == 'Export')
                    expected = f'"field=capability:{capability}"' if reject else '""'
                    checks.append(f'  check "{owner}_{action}_{mode}" ({audit} env ``{stem}{mode} env.header.mainModule) {expected}\n')
        probe.write_text(imports + '''import LeanInformationAudit.Projection.OutputOnlyAudit
open Lean Elab Command LeanInformationAudit
''' + ''.join(declarations) + '''
run_cmd do
  let env ← getEnv
  let check (label : String) (actual : Except String Unit) (expected : String) : CommandElabM Unit := do
    let ok := match actual with
      | .ok () => expected.isEmpty
      | .error message => !expected.isEmpty && (message.splitOn expected).length == 2
    unless ok do throwError "[FAIL] {label}: {repr actual}"
''' + ''.join(f'''  unless (env.getModuleIdxFor? ``{namespace}.read).map (env.allImportedModuleNames[·.toNat]!) ==
      some `{owner}.OwnerProbe do throwError "[FAIL] compiler_owner_{owner}"
''' for owner, namespace in owners) + ''.join(checks) +
                         '  logInfo "[PASS] compiler_owner_audits cases=75"\n')
        with (package / 'lakefile.toml').open('a') as config:
            for owner, _ in owners[1:]:
                config.write(f'\n[[lean_lib]]\nname = "{owner}"\nglobs = ["{owner}.+"]\n')
        result = self.guarded_command([self.lake, 'build', 'LeanInformationAudit.OwnerConsumer'],
                                      cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('[PASS] compiler_owner_audits cases=75', result.stdout)

    def test_interface_registered_build_inputs(self):
        selection = publication.selection.Selection(ROOT)
        package = ROOT / 'tools/lean-inspector-interface'
        sources = {str(path.relative_to(ROOT)) for path in package.rglob('*.lean')
                   if '.lake' not in path.parts}
        contract = package / 'LeanInformationAuditInterface/Contract'
        sources.update(str(path.relative_to(ROOT)) for path in contract.glob('*.lean'))
        self.assertTrue(any(path.startswith(str(contract.relative_to(ROOT))) for path in sources))
        self.assertTrue(sources)
        self.assertTrue(sources <= set(selection.expand('inspector_sources')))
        self.assertTrue(sources <= set(selection.dependency_sources()))
        self.assertFalse(sources & set(selection.modules().values()))
        for name in ('lakefile.toml', 'lake-manifest.json'):
            path = 'tools/lean-inspector-interface/' + name
            self.assertIn(path, selection.expand('config_inputs'))
            self.assertIn(dict(pattern=path, optional=False),
                          selection.data['config_inputs']['include'])

    def interface_package(self):
        source = ROOT / 'tools/lean-inspector-interface'
        self.assertTrue(source.is_dir(), 'missing standalone declaration Interface package')
        package = self.root / 'interface package'
        policy = tomllib.loads((source / 'lakefile.toml').read_text())
        self.assertEqual(policy.get('require', []), [{'name': 'trureturing', 'path': '../..'}])
        copy_contract_interface(source, package)
        shutil.copyfile(ROOT / 'lean-toolchain', package / 'lean-toolchain')
        config = package / 'lakefile.toml'
        policy = tomllib.loads(config.read_text())
        self.assertEqual(policy.get('require', []), [], 'Recorder fixture must have zero requires')
        self.assertEqual(json.loads((package / 'lake-manifest.json').read_text())['packages'], [])
        self.assertEqual(len(policy['lean_lib']), 1)
        # The production output is transported under the repository buildDir.
        # An isolated copy must keep both artifacts and Lake metadata in its temp root.
        self.assertTrue((source / policy['buildDir']).resolve().is_relative_to(ROOT / '.lake/build'))
        config.write_text(re.sub(r'(?m)^buildDir\s*=.*$', 'buildDir = ".lake/build"',
            re.sub(r'(?m)^packagesDir\s*=.*$', 'packagesDir = ".lake/packages"', config.read_text())))
        manifest = package / 'lake-manifest.json'
        resolved = json.loads(manifest.read_text())
        resolved['packagesDir'] = '.lake/packages'
        manifest.write_text(json.dumps(resolved))
        env = {key: value for key, value in os.environ.items()
               if not key.startswith(('LEAN_', 'LAKE_', 'ELAN_'))}
        return package, env

    def test_interface_standalone_core_only(self):
        package, env = self.interface_package()
        result = self.guarded_command([self.lake, 'build'], cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_interface_typed_inputs_compile_without_judge(self):
        package, env = self.interface_package()
        built = self.guarded_command([self.lake, 'build'], cwd=package, env=env)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        (package / 'TypedInputs.lean').write_text('''import LeanInformationAuditInterface.Contract.Catalog
open LeanInformationAudit
def rootInput : Contract.RootCatalog := { data := {
  rootId := `TypedInputs, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def templateInput : Contract.TemplateEnrollment Nat := {
  name := `Nat, version := 1, constructors := #[], options := #[] }
''')
        result = self.guarded_command([self.lake, 'env', 'lean', 'TypedInputs.lean'], cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn('IE-C050', result.stdout + result.stderr)
