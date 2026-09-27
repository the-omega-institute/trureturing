"""The declaration package must build with only the installed core toolchain."""
import json
import os
import re
import shutil
import tomllib

from test_native_support import ROOT, publication


class NativeInterfaceTests:
    def test_output_audit_follows_compiler_package_owners(self):
        package, env = self.interface_package()
        for relative in ('Projection/OutputOnlyAudit.lean', 'Registry/Repository.lean'):
            source = ROOT / 'tools/lean-inspector/LeanInformationAudit' / relative
            target = package / 'LeanInformationAudit' / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
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
                declarations.append(f'''def {stem}Publication : CommandElabM Unit := {namespace}.{action}
def {stem}Seal : CommandElab := terminalSealCommand {stem}Publication
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
        shutil.copytree(source, package, ignore=shutil.ignore_patterns('.lake'))
        shutil.copyfile(ROOT / 'lean-toolchain', package / 'lean-toolchain')
        config = package / 'lakefile.toml'
        policy = tomllib.loads(config.read_text())
        self.assertEqual(policy.get('require', []), [], 'Interface must have zero requires')
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

    def test_interface_only_reports_missing_handler(self):
        package, env = self.interface_package()
        built = self.guarded_command([self.lake, 'build'], cwd=package, env=env)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        (package / 'MissingHandler.lean').write_text(
            'import LeanInformationAuditInterface.Syntax\n'
            'def output := 1\ndef analysis_output := 2\ndef ascii_output := 3\n'
            'register_information_template Nat\n')
        result = self.guarded_command([self.lake, 'env', 'lean', 'MissingHandler.lean'],
                                      cwd=package, env=env)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('elaboration function', result.stdout + result.stderr)
        self.assertNotIn('unexpected token', result.stdout + result.stderr)

    def test_interface_grammar_has_single_owner(self):
        implementation = ROOT / 'tools/lean-inspector/LeanInformationAudit/Syntax.lean'
        source = implementation.read_text()
        grammar = r'(?m)^\s*(syntax\b|declare_syntax_cat\b|elab\s)'
        self.assertFalse(re.search(grammar, source), 'implementation still declares registration grammar')
        self.assertNotRegex(source, r'(?m)^\s*def\s+(registrationTerm|\w+Keyword)\b')
        self.assertIn('run_cmd TemplateAudit.initializeGrammarPins', source)
        output_audit = implementation.parent / 'Projection/OutputOnlyAudit.lean'
        self.assertFalse(re.search(grammar, output_audit.read_text()),
                         'output-only audit still declares command grammar')
