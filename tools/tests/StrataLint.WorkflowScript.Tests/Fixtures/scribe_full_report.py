"""Exercise make emit with real full-bundle currency and material verification."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector/tests'))
import test_reuse as reuse_fixture

publication = reuse_fixture.publication
materials = reuse_fixture.materials


class ScribeFullReportContracts(unittest.TestCase):
    def setUp(self):
        self.fixture = reuse_fixture.ReuseTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root, self.report = self.fixture.root, self.fixture.report
        for name in ('Makefile', 'tools/scripts/scribe.sh',
                     'tools/scripts/report/report-consumer.sh',
                     'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                     'tools/lean-inspector/fib_analysis.py'):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)
            target.chmod(0o755)
        self.executable('tools/scripts/report/report-supervisor.sh',
            '#!/bin/bash\n[[ "$1" == --role && "$2" == scribe-consumer && "$3" == -- ]] || exit 93\n'
            'shift 3\nexec "$@"\n')
        for tool in ('lean', 'lake'):
            self.executable('bin/' + tool, '#!/bin/bash\necho unexpected Lean invocation >&2\nexit 94\n')
        self.executable('bin/dotnet', '''#!/usr/bin/env python3
import json, os, pathlib, sys
args = sys.argv[1:]
root = pathlib.Path(os.environ['FIXTURE_ROOT'])
report = os.environ.get('STRATALINT_LEAN_REPORT')
with (root / 'calls.jsonl').open('a') as log:
    log.write(json.dumps(dict(args=args, report=report)) + '\\n')
if args[0] == 'build':
    sys.exit(0)
if args[1] == 'emit':
    assert '--scoped' not in args and '--paths-from' in args
    selected = pathlib.Path(args[args.index('--paths-from') + 1])
    assert selected.read_bytes() == b'Blueprint/D5/A.scribe.cs\\0'
    snapshot = pathlib.Path(report)
    original = root / 'seed/raw-lean-report.json'
    assert snapshot != original and snapshot.name == original.name
    expected = json.loads((root / 'expected.json').read_text())
    if os.environ.get('MUTATE_BUNDLE') == '1':
        for suffix in expected:
            pathlib.Path(str(original) + suffix).write_bytes(b'later producer bytes')
    for suffix, value in expected.items():
        assert pathlib.Path(str(snapshot) + suffix).read_bytes().hex() == value
elif args[1] != 'emit-values':
    raise AssertionError('unexpected dotnet invocation: ' + repr(args))
''')
        self.paths = self.root / 'selected paths'
        self.paths.write_bytes(b'Blueprint/D5/A.scribe.cs\0')
        self.fixture.bundle()
        row = json.loads(self.report.read_bytes())['modules'][0]
        material = 'Nat'
        self.material_name = 'sha256/' + materials.statement_address(material.encode())[7:]
        row['declarations'] = [dict(axioms=[], include_in_statement=True, kind='def',
            name='a', name_key='a', type_sha256='sha256:' + self.material_name[7:],
            statement_id=materials.declaration_statement_id('D5/A.lean', 'def', 'a', material))]
        self.seal(row)
        with zipfile.ZipFile(publication.member(self.report, '.materials.zip'), 'w') as archive:
            archive.writestr(self.material_name, material)
        self.expected = {suffix: publication.member(self.report, suffix).read_bytes()
                         for suffix in publication.SUFFIXES}
        (self.root / 'expected.json').write_text(json.dumps(
            {suffix: value.hex() for suffix, value in self.expected.items()}))

    def executable(self, name, source):
        self.fixture.write(name, source)
        (self.root / name).chmod(0o755)

    def seal(self, row):
        report = dict(schema=materials.REPORT_SCHEMA, modules=[row])
        self.report.write_bytes(materials.canonical_json(report))
        origins = json.loads(publication.member(self.report, '.provenance.json').read_bytes())['module_origins']
        origins[row['module']]['report_sha256'] = hashlib.sha256(materials.canonical_json(report)).hexdigest()
        publication.write_sidecars(self.report, publication.coordinates(self.root), origins)

    def emit(self, *, relative=False, mutate=False):
        log = self.root / 'calls.jsonl'
        log.unlink(missing_ok=True)
        report = self.report.relative_to(self.root) if relative else self.report
        environment = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'],
            FIXTURE_ROOT=str(self.root), MUTATE_BUNDLE=str(int(mutate)))
        result = subprocess.run(['/usr/bin/make', 'emit', 'PATHS=' + str(self.paths),
            'EMIT_FULL_REPORT=' + str(report)], cwd=self.root, env=environment,
            capture_output=True, text=True, timeout=60)
        self.calls = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
        return result

    def rejected(self):
        result = self.emit()
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([call['args'][0] for call in self.calls], ['build'])

    def test_absolute_and_relative_paths_use_full_report_without_lean(self):
        for relative in (False, True):
            with self.subTest(relative=relative):
                result = self.emit(relative=relative)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual([call['args'][1] for call in self.calls[1:]], ['emit', 'emit-values'])
                for suffix, value in self.expected.items():
                    self.assertEqual(publication.member(self.report, suffix).read_bytes(), value)

    def test_emitter_reads_all_members_from_the_same_private_snapshot(self):
        result = self.emit(mutate=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.report.read_bytes(), b'later producer bytes')
        self.assertFalse(Path(self.calls[1]['report']).exists(), 'private snapshot must be cleaned')

    def test_missing_bundle_members_are_rejected(self):
        for suffix, value in self.expected.items():
            with self.subTest(suffix=suffix):
                member = publication.member(self.report, suffix)
                member.unlink()
                try:
                    self.rejected()
                finally:
                    member.write_bytes(value)

    def test_changed_source_or_toolchain_is_rejected(self):
        for name in ('D5/A.lean', 'lean-toolchain', 'lakefile.toml'):
            with self.subTest(input=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b'changed\n')
                try:
                    self.rejected()
                finally:
                    path.write_bytes(original)

    def test_corrupt_report_hash_attestation_or_origin_is_rejected(self):
        for suffix in ('', '.sha256', '.input.attestation', '.provenance.json'):
            with self.subTest(suffix=suffix):
                member = publication.member(self.report, suffix)
                if suffix == '.provenance.json':
                    value = json.loads(member.read_bytes())
                    value['module_origins']['D5.A']['report_sha256'] = '0' * 64
                    member.write_text(json.dumps(value))
                else:
                    member.write_bytes(b'corrupt\n')
                try:
                    self.rejected()
                finally:
                    member.write_bytes(self.expected[suffix])

    def test_corrupt_missing_or_unreferenced_material_is_rejected(self):
        member = publication.member(self.report, '.materials.zip')
        for defect in ('archive', 'content', 'missing', 'unreferenced'):
            with self.subTest(defect=defect):
                if defect == 'archive':
                    member.write_bytes(b'not a ZIP archive')
                else:
                    with zipfile.ZipFile(member, 'w') as archive:
                        if defect != 'missing':
                            archive.writestr(self.material_name, 'corrupt' if defect == 'content' else 'Nat')
                        if defect == 'unreferenced':
                            archive.writestr('extra', 'unreferenced')
                self.rejected()

    def test_resealed_report_with_mismatched_statement_identity_is_rejected(self):
        row = json.loads(self.report.read_bytes())['modules'][0]
        row['declarations'][0]['statement_id'] = 'sha256:' + '0' * 64
        self.seal(row)
        self.rejected()

    def test_full_material_validation_cannot_be_combined_with_scoped_targets(self):
        result = subprocess.run(['/bin/bash', str(self.root / 'tools/scripts/report/report-consumer.sh'),
            '--validate-materials', '--targets', 'D5.A'], capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 2)
        self.assertIn('requires a full report', result.stderr)


if __name__ == '__main__':
    unittest.main(verbosity=2)
