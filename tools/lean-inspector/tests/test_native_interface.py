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
        for relative in ('BindingRecords.lean', 'EscapeEvidence.lean'):
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
                declarations.append(f'''def {stem}Publication (_ : ValidatedSourceSnapshot) : CommandElabM Unit := {namespace}.{action}
def {stem}Seal : ValidatedSourceSnapshot → CommandElab := terminalSealCommand {stem}Publication
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

    def test_interface_only_records_unassessed_inputs(self):
        package, env = self.interface_package()
        built = self.guarded_command([self.lake, 'build'], cwd=package, env=env)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        (package / 'MissingHandler.lean').write_text(
            'import LeanInformationAuditInterface.Syntax\n'
            'def output := 1\ndef analysis_output := 2\ndef ascii_output := 3\n'
            'register_information_template Nat\n')
        result = self.guarded_command([self.lake, 'env', 'lean', 'MissingHandler.lean'],
                                      cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn('IE-C050', result.stdout + result.stderr)

    def test_interface_grammar_has_single_owner(self):
        implementation = ROOT / 'tools/lean-inspector/LeanInformationAudit/Syntax.lean'
        self.assertFalse(implementation.exists(), 'retired implementation elaborator remains')
        source = (ROOT / 'tools/lean-inspector/LeanInformationAudit/Registry.lean').read_text()
        grammar = r'(?m)^\s*(syntax\b|declare_syntax_cat\b|elab\s)'
        self.assertFalse(re.search(grammar, source), 'implementation still declares registration grammar')
        self.assertNotRegex(source, r'(?m)^\s*def\s+(registrationTerm|\w+Keyword)\b')
        self.assertIn('run_cmd LeanInformationAudit.TemplateAudit.initializeGrammarPins', source)
        output_audit = implementation.parent / 'Projection/OutputOnlyAudit.lean'
        self.assertFalse(re.search(grammar, output_audit.read_text()),
                         'output-only audit still declares command grammar')

    def test_interface_recorder_holds_no_admission_policy(self):
        # Reg compiles against the interface only; an admission rule held there
        # would make a judge-policy change rebuild every Reg module. The two
        # rules once duplicated in the recorder are owned by the report.
        interface = ROOT / 'tools/lean-inspector-interface/LeanInformationAuditInterface'
        recorder = '\n'.join(path.read_text() for path in sorted(interface.rglob('*.lean')))
        for policy in ('IE-C011', 'isCompanionName', 'generatedCompanionSuffixes',
                       '__lowers_escape', '__catalog_irredundant', 'RigidUniverseMismatch',
                       'P1.ArenaMismatch'):
            self.assertNotIn(policy, recorder, f'[FAIL] recorder_holds_policy:{policy}')
        judge = ROOT / 'tools/lean-inspector/LeanInformationAudit'
        entries = (judge / 'Registry/Entries.lean').read_text()
        self.assertIn('def generatedCompanionSuffixes', entries)
        self.assertIn('IE-C011 GeneratedCertificateRegistered', entries)
        self.assertIn('P1.RigidUniverseMismatch: arena must have three zero universe levels',
                      (judge / 'Registry/Reifier.lean').read_text())

    def test_interface_records_definition_bridge_before_assessment(self):
        # Exercise the production recorder, without importing any judge module.
        # These core-only types supply its companion ABI; the full D5/report
        # service pair is exercised by RecorderPolicyInputs/Boundary in Lean.
        package, env = self.interface_package()
        with (package / 'lakefile.toml').open('a') as config:
            config.write('\n[[lean_lib]]\nname = "RecorderInputs"\n'
                         '\n[[lean_lib]]\nname = "RecorderConsumer"\n')
        (package / 'RecorderInputs.lean').write_text('''import LeanInformationAuditInterface.Syntax
namespace D5.S3.ConceptDynamics.InformationEscape
structure Arena where
  State : Type
  stateDecidableEq : DecidableEq State
structure PrimitiveSignature where
  marker : Bool
structure PrimitiveBundle (State : Type) where
  marker : Bool
structure PrimitiveRealization (State : Type) (signature : PrimitiveSignature) where
  marker : Bool
def PrimitiveRealization.toPrimitiveBundle {State : Type} {signature : PrimitiveSignature}
    [DecidableEq State] (r : PrimitiveRealization State signature) : PrimitiveBundle State :=
  ⟨r.marker⟩
structure PrimitiveLawArena where
  toArena : Arena
  signature : PrimitiveSignature
structure LegacyPrimitiveRealization (arena : PrimitiveLawArena) (Statement : Prop)
    (r : PrimitiveRealization arena.toArena.State arena.signature) : Prop where
  proof : Statement
structure TheoremUnit (arena : Arena) where
  primitives : PrimitiveBundle arena.State
  Statement : Prop
  proof : Statement
def LegacyPrimitiveRealization.toTheoremUnit {arena : PrimitiveLawArena} {Statement : Prop}
    {r : PrimitiveRealization arena.toArena.State arena.signature}
    (_bridge : LegacyPrimitiveRealization arena Statement r) (proof : Statement) :
    TheoremUnit arena.toArena := ⟨⟨r.marker⟩, Statement, proof⟩
end D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape
def arena : PrimitiveLawArena := ⟨⟨Bool, inferInstance⟩, ⟨false⟩⟩
def reads : PrimitiveRealization Bool arena.signature := ⟨false⟩
theorem target : True := trivial
theorem occurrenceTarget : True := trivial
set_option linter.defProp false in
def bridge : LegacyPrimitiveRealization arena True reads := ⟨trivial⟩
register_information_theorem target in arena
  primitives reads.toPrimitiveBundle realization bridge
def objectArena := arena.toArena
register_information_theorem occurrenceTarget in arena
  object_arena objectArena catalog definitionBridge
  primitives reads.toPrimitiveBundle realization bridge
''')
        recorded = self.guarded_command([self.lake, 'build', 'RecorderInputs'],
                                        cwd=package, env=env)
        self.assertEqual(recorded.returncode, 0,
                         '[FAIL] recorder_rejected_typed_definition_bridge\n' +
                         recorded.stdout + recorded.stderr)
        # A fresh consumer reads the persisted inputs, after recording completed.
        # No test_assess wrapper can turn a recording error into a passing guard.
        (package / 'RecorderConsumer.lean').write_text('''import RecorderInputs
open Lean Elab Command LeanInformationAudit
run_cmd do
  let env ← getEnv
  let inputs := (RegistrationInputs.owned env).filter (·.1 == `RecorderInputs)
  unless inputs.size == 2 do throwError "[FAIL] definition_bridge_inputs_not_persisted"
  let .defnInfo _ ← getConstInfo ``bridge | throwError "[FAIL] bridge_kind_changed"
  for (_, input) in inputs do
    let unit ← getConstInfo input.entry.unitName
    unless !unit.type.hasMVar && !unit.type.hasFVar do
      throwError "[FAIL] definition_bridge_companion_not_closed"
    discard <| getConstInfo input.entry.realizationName
  logInfo "[PASS] typed_definition_bridge_recorded_and_imported count=2"
''')
        consumed = self.guarded_command([self.lake, 'build', 'RecorderConsumer'],
                                        cwd=package, env=env)
        self.assertEqual(consumed.returncode, 0, consumed.stdout + consumed.stderr)
        self.assertIn('[PASS] typed_definition_bridge_recorded_and_imported count=2', consumed.stdout)
