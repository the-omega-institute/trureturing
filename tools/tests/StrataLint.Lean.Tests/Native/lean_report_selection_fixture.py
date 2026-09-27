"""Declared synthetic inputs for the report selection consumers; no repository scan."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
import zipfile

ROOT, SCRATCH, SCENARIO = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
MANIFEST = 'lean-report-inputs.json'
LOADER = 'tools/scripts/report/lean-report-selection.py'
INPUT = 'tools/scripts/report/lean-report-input.sh'


def spec(pattern, optional=False):
    return dict(pattern=pattern, optional=optional)


def paths(*patterns):
    return dict(include=[spec(p) for p in patterns], exclude=[])


def declaration():
    return dict(schema_version=1, report_cache_release_semantic_version=1,
        report_modules=dict(include=[spec('Trureturing.lean'), spec('D5/**/*.lean', True)], exclude=[]),
        inspector_sources=dict(include=[spec('tools/lean-inspector/**/*.lean', True),
            spec('tools/lean-inspector-interface/**/*.lean', True)], exclude=[]),
        dependency_sources=dict(include=[spec('tools/lean-inspector/**/*.lean', True),
            spec('tools/lean-inspector-interface/**/*.lean', True)], exclude=[]),
        config_inputs=paths('lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
            'tools/lean-inspector-interface/lakefile.toml',
            'tools/lean-inspector-interface/lake-manifest.json'),
        producer_scopes={
            'lean-report': paths(MANIFEST, LOADER, INPUT, 'tools/lean-inspector/inspect.sh',
                'tools/lean-inspector/native.py', 'tools/lean-inspector/materials.py', 'Engine/**/*.cs'),
            'scribe-content': dict(include=[spec('Blueprint/**/*.scribe.cs', True)], exclude=[])})


class Contract(unittest.TestCase):
    def setUp(self):
        self.repo = SCRATCH / self._testMethodName
        self.repo.mkdir(parents=True, exist_ok=True)
        self.policy = declaration()
        for path, text in {
                'Trureturing.lean': 'import D5.Consumer\n',
                'D5/Base.lean': 'def base := 1\n', 'D5/Claim.lean': 'import D5.Base\n',
                'D5/Consumer.lean': '-- no import: header claim is a report dependency\n',
                'D5/Alone.lean': 'def alone := 1\n', 'Engine/Main.cs': '// producer\n',
                'lean-toolchain': 'leanprover/lean4:v4.33.0\n',
                'lake-manifest.json': '{}\n', 'lakefile.toml': 'name = "fixture"\n',
                'tools/lean-inspector/Inspector.lean': '-- inspector\n',
                'tools/lean-inspector-interface/LeanInformationAuditInterface/Syntax.lean': '-- grammar\n',
                'tools/lean-inspector-interface/lakefile.toml': 'name = "interface"\n',
                'tools/lean-inspector-interface/lake-manifest.json': '{"packages": []}\n',
                'Blueprint/Probe.scribe.cs': '// document\n'}.items():
            self.write(path, text)
        for relative in (LOADER, INPUT, 'tools/scripts/worktree/lean-cache-input.sh',
                'tools/lean-inspector/inspect.sh', 'tools/lean-inspector/native.py',
                'tools/lean-inspector/materials.py', 'tools/scripts/lib/resource-observation-lib.sh'):
            self.write(relative, (ROOT / relative).read_text())
        self.save()
        module_spec = importlib.util.spec_from_file_location('selection', self.repo / LOADER)
        self.loader = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(self.loader)

    def write(self, path, text):
        target = self.repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def save(self):
        self.write(MANIFEST, json.dumps(self.policy))

    def selection(self):
        self.save()
        return self.loader.Selection(self.repo)

    def run_input(self, command='address'):
        return subprocess.run(['bash', str(self.repo / INPUT), command, '--repository', str(self.repo)],
            cwd=SCRATCH, text=True, capture_output=True,
            env=dict(os.environ, TMPDIR=str(SCRATCH), STRATALINT_LEAN_INPUT_MEMO_ROOT=str(SCRATCH / 'memo')))

    def address(self):
        self.save()
        result = self.run_input()
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.strip().split(' ')

    def test_registration_failures(self):
        mutations = [
            ('schema_version', lambda p: p.update(schema_version=99)),
            ('unexpected', lambda p: p.update(unexpected=[])),
            ('unknown-scope', lambda p: p['producer_scopes'].update({'unknown-scope': paths()})),
            ('../escape', lambda p: p['config_inputs']['include'].append(spec('../escape'))),
            ('missing.txt', lambda p: p['producer_scopes']['lean-report']['include'].append(spec('missing.txt'))),
            (LOADER, lambda p: p['producer_scopes']['lean-report']['include'].pop(1)),
        ]
        for expected, mutate in mutations:
            with self.subTest(expected=expected):
                self.policy = declaration()
                mutate(self.policy)
                with self.assertRaisesRegex(ValueError, expected.replace('.', r'\.')):
                    self.selection().validate('lean-report')
        self.policy = declaration()
        self.save()
        (self.repo / MANIFEST).unlink()
        result = self.run_input()
        self.assertEqual(result.returncode, 2)
        self.assertIn(MANIFEST, result.stderr)
        self.assertEqual(result.stdout, '')

    def test_reg_module_name(self):
        self.policy['report_modules']['include'].append(spec('Reg/**/*.lean', True))
        before = self.selection().modules()
        self.assertFalse(any(name.startswith('Reg.') for name in before))
        self.write('Reg/D5/S3/Arith/X.lean', '-- registration module\n')
        modules = self.selection().modules()
        self.assertEqual(modules['Reg.D5.S3.Arith.X'], 'Reg/D5/S3/Arith/X.lean')
        self.assertEqual({k: v for k, v in modules.items() if k != 'Reg.D5.S3.Arith.X'}, before)

    def test_glob_semantics(self):
        for pattern, yes, no in [
                ('*.cs', ['A.cs'], ['Dir/A.cs', 'A.CS']),
                ('Src/**/*.cs', ['Src/A.cs', 'Src/Sub/A.cs'], ['Src/A.CS', 'Other/A.cs']),
                ('Src/**.cs', ['Src/A.cs', 'Src/Sub/A.cs'], ['Src/A.txt']),
                ('Src/[x].cs', ['Src/[x].cs'], ['Src/x.cs'])]:
            matcher = self.loader.compile_glob(pattern, 'fixture')
            for path in yes: self.assertTrue(matcher.fullmatch(path), (pattern, path))
            for path in no: self.assertFalse(matcher.fullmatch(path), (pattern, path))
        self.write('Engine/bin/Generated.cs', '// excluded')
        self.write('Engine/obj/Generated.cs', '// excluded')
        self.write('Engine/Nested/Extra.cs', '// included')
        selected = self.policy['producer_scopes']['lean-report']
        selected['include'] += [spec('Engine/Main.cs'), spec('absent.txt', True), spec('Growth/**/*.cs', True)]
        selected['exclude'] = ['**/bin/**', '**/obj/**']
        selection = self.selection()
        actual = selection.producer_paths('lean-report')
        self.assertIn('Engine/Nested/Extra.cs', actual)
        self.assertNotIn('Engine/bin/Generated.cs', actual)
        self.assertNotIn('Engine/obj/Generated.cs', actual)
        self.assertEqual(actual.count('Engine/Main.cs'), 1)
        self.assertEqual(actual, sorted(actual))

    def test_source_and_policy_identity(self):
        before = self.address()
        self.write('D5/AloneNew.lean', 'def next := 2\n')
        added = self.address()
        self.assertEqual(before[1], added[1])
        self.assertNotEqual(before[2], added[2])
        (self.repo / 'D5/Alone.lean').rename(self.repo / 'D5/AloneRenamed.lean')
        renamed = self.address()
        self.assertEqual(added[1], renamed[1])
        self.assertNotEqual(added[2], renamed[2])
        self.write('Blueprint/Probe.scribe.cs', '// new document')
        self.assertEqual(renamed, self.address())
        self.policy['producer_scopes']['scribe-content']['include'].append(spec('ScribeExtra.cs', True))
        self.assertEqual(renamed, self.address())
        self.policy['producer_scopes']['lean-report']['include'].append(spec('Extra.py', True))
        policy = self.address()
        self.assertEqual(renamed, policy)
        self.assertEqual(renamed[2:], policy[2:])
        self.write('Engine/Main.cs', '// producer changed')
        producer = self.address()
        self.assertEqual(policy, producer)
        self.write('tools/lean-inspector-interface/LeanInformationAuditInterface/Syntax.lean', '-- compatible grammar\n')
        self.assertEqual(producer, self.address())
        interface_source = 'tools/lean-inspector-interface/LeanInformationAuditInterface/Syntax.lean'
        self.assertIn(interface_source, self.selection().expand('inspector_sources'))
        self.assertIn(interface_source, self.selection().dependency_sources())
        self.write('tools/lean-inspector-interface/lakefile.toml', 'name = "changedInterface"\n')
        interface_config = self.address()
        self.assertNotEqual(producer[3], interface_config[3])
        self.assertEqual(producer[1:3], interface_config[1:3])
        producer = interface_config
        self.policy['report_cache_release_semantic_version'] = 2
        bumped = self.address()
        self.assertNotEqual(producer[1], bumped[1])
        self.assertEqual(producer[2:], bumped[2:])
        self.write('lean-toolchain', 'changed pin')
        config = self.address()
        self.assertNotEqual(producer[3], config[3])
        self.assertEqual(producer[2], config[2])

    def test_source_traversal_io(self):
        self.assertNotEqual(os.getuid(), 0, 'requires a non-root POSIX process')
        baseline = self.address()
        self.write('D5/BaseAdded.lean', 'def added := 2\n')
        directory = self.repo / 'D5'
        try:
            directory.chmod(0)
            inaccessible = self.run_input()
            self.assertEqual(inaccessible.returncode, 2, inaccessible.stderr)
            self.assertIn('registered source traversal failed', inaccessible.stderr)
            self.assertEqual(inaccessible.stdout, '')
        finally:
            directory.chmod(0o700)
        self.assertNotEqual(self.address(), baseline)
        self.assertIn('D5.BaseAdded', self.run_input('modules').stdout)

if __name__ == '__main__':
    unittest.main(argv=[sys.argv[0], 'Contract.test_' + SCENARIO])
