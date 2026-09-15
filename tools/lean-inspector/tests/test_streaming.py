"""Byte and failure regressions for the statement-v1 stream contract."""
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import materials
import publication


class StreamingTests(unittest.TestCase):
    def test_chunk_boundaries_match_canonical_declaration_bytes(self):
        values = ['', 'plain', '\\"\n\x00λ😀𐀀\U0010ffff', '\b\t\r\f' + 'a' * 65530 + '😀tail']
        for value in values:
            for size in [1, 2, 3, 4, 5, 7, 64, 65536]:
                with self.subTest(length=len(value), chunk=size):
                    expected = materials.declaration_statement_id('X.lean', 'def', 'ns(n0,1:x)', value)
                    actual = materials.material_identities(io.BytesIO(value.encode()), 'X.lean', 'def', 'ns(n0,1:x)', size)
                    self.assertEqual(actual, (materials.statement_address(value.encode()), expected))

    def test_supplementary_scalars_have_uppercase_surrogate_bytes(self):
        self.assertEqual(materials.canonical_json({'s': 'λ😀𐀀\U0010ffff'}),
                         '{"s": "λ\\uD83D\\uDE00\\uD800\\uDC00\\uDBFF\\uDFFF"}\n'.encode())

    def test_bmp_controls_and_unicode_metadata_match_canonical_identity(self):
        value = ''.join(chr(n) for n in range(128)) + 'λ\u07ff\u0800\u2028\u2029\ud7ff\ue000\ufffe\uffff'
        path, key = 'Δ😀.lean', 'ns(λ,\"\\\t𐀀)'
        expected = materials.declaration_statement_id(path, 'def', key, value)
        for size in [1, 2, 3, 7, 64, materials.BUFFER_BYTES]:
            with self.subTest(chunk=size):
                self.assertEqual(materials.material_identities(io.BytesIO(value.encode()), path, 'def', key, size),
                                 (materials.statement_address(value.encode()), expected))

    def test_strict_utf8_rejects_overlong_surrogate_invalid_and_truncated_sequences(self):
        for invalid in [b'\xc0\xaf', b'\xed\xa0\x80', b'\xf4\x90\x80\x80', b'\x80', b'\xf0\x9f\x98', b'\xe2\x82', b'\xc2']:
            for size in [1, 2, 3, 4, 7]:
                with self.subTest(invalid=invalid, chunk=size):
                    with self.assertRaises(UnicodeDecodeError):
                        materials.material_identities(io.BytesIO(b'x' * 7 + invalid), 'X.lean', 'def', 'key', size)

    def test_reads_are_bounded_even_for_a_large_single_material(self):
        class Bounded(io.BytesIO):
            def read(self, count=-1):
                self.assertion(count)
                return super().read(count)
            def assertion(self, count):
                if not 0 < count <= materials.BUFFER_BYTES:
                    raise AssertionError(count)
        source = Bounded(('λ😀x' * 300000).encode())
        actual = materials.material_identities(source, 'X.lean', 'opaque', 'key')
        self.assertEqual(actual[0], materials.statement_address(source.getvalue()))

    def test_duplicate_json_fields_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            publication.read_json('{"modules": [], "modules": []}')

    def test_stream_comparison_detects_collision_after_chunk_boundary(self):
        prefix = b'x' * (materials.BUFFER_BYTES + 7)
        self.assertTrue(materials.streams_equal(io.BytesIO(prefix), io.BytesIO(prefix)))
        self.assertFalse(materials.streams_equal(io.BytesIO(prefix + b'a'), io.BytesIO(prefix + b'b')))
        self.assertFalse(materials.streams_equal(io.BytesIO(prefix), io.BytesIO(prefix + b'b')))

    def test_compactor_rejects_duplicate_spool_and_hash_collision(self):
        for duplicate in [True, False]:
            with self.subTest(duplicate=duplicate), tempfile.TemporaryDirectory() as directory:
                directory = Path(directory)
                spool = directory / 'spool'
                spool.mkdir()
                (spool / '0.statement').write_text('first')
                (spool / '1.statement').write_text('second')
                declarations = [dict(axioms=[], include_in_statement=False, kind='theorem',
                    material_file=('0.statement' if duplicate else str(n) + '.statement'), name=str(n), name_key=str(n)) for n in range(2)]
                report = directory / 'spool.json'
                report.write_text(json.dumps(dict(schema=materials.SPOOL_SCHEMA, modules=[dict(module='X',
                    source_path='X.lean', source_sha256='sha256:' + 'a' * 64, imports=[], declarations=declarations)])))
                output = directory / 'report.json'
                with patch.object(materials, 'material_identities', return_value=('sha256:' + 'b' * 64, 'sha256:' + 'c' * 64)):
                    with self.assertRaisesRegex(ValueError, 'reused|collision'):
                        materials.compact(report, spool, output)
                self.assertFalse(output.exists())



class PublicationTests(unittest.TestCase):
    def test_shared_validation_rechecks_bytes_and_complete_declaration_identity(self):
        import zipfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spool = root / 'spool'
            spool.mkdir()
            (spool / '0.statement').write_text('λ😀' * (materials.BUFFER_BYTES + 1))
            source = root / 'spool.json'
            source.write_text(json.dumps(dict(schema=materials.SPOOL_SCHEMA, modules=[dict(
                module='X', source_path='X.lean', source_sha256='sha256:' + 'a'*64, imports=[],
                declarations=[dict(axioms=[], include_in_statement=False, kind='opaque',
                    material_file='0.statement', name='x', name_key='ns(n0,1:x)')])])) )
            report = root / 'report.json'
            archive = publication.member(report, '.materials.zip')
            materials.compact(source, spool, report)
            verified = {}
            with patch.object(materials, 'material_identities', wraps=materials.material_identities) as identities:
                rows = publication.validate_rows(report, archive, verified)
                publication.validate_rows(report, archive, verified)
                self.assertEqual(identities.call_count, 1)
                original = report.read_bytes()
                rows[0]['declarations'][0]['statement_id'] = 'sha256:' + 'b'*64
                report.write_bytes(materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=rows)))
                with self.assertRaisesRegex(ValueError, 'identity mismatch'):
                    publication.validate_rows(report, archive, verified)
                report.write_bytes(original)
                with zipfile.ZipFile(archive) as reader:
                    name = reader.namelist()[0]
                with zipfile.ZipFile(archive, 'w') as writer:
                    writer.writestr(name, b'corrupt actual bytes')
                with self.assertRaisesRegex(ValueError, 'material address mismatch'):
                    publication.validate_rows(report, archive, verified)

    def test_source_membership_and_claim_bindings_use_current_registered_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'X.lean'
            source.write_text('def x : Nat := 1\n')
            claim = root / 'Claim.lean'
            claim.write_text('def claim : Prop := False\n')
            paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
            (root / 'lean-report-inputs.json').write_text(json.dumps(dict(schema_version=1, report_semantic_version=1,
                report_modules=paths('X.lean'), inspector_sources=paths(), config_inputs=paths(),
                producer_scopes={'lean-report': paths('lean-report-inputs.json',
                    'tools/scripts/report/lean-report-selection.py'), 'scribe-content': paths()})))
            row = dict(module='X', source_path='X.lean', source_sha256='sha256:' + publication.digest(source),
                utility_refutation=dict(claim_source_path='Claim.lean', claim_source_sha256='sha256:' + publication.digest(claim)))
            publication.validate_sources([row], root)
            with self.assertRaisesRegex(ValueError, 'membership'):
                publication.validate_sources([], root)
            row['source_path'] = 'Claim.lean'
            with self.assertRaisesRegex(ValueError, 'source binding'):
                publication.validate_sources([row], root)
            row['source_path'] = 'X.lean'
            claim.write_text('def claim : Prop := True\n')
            with self.assertRaisesRegex(ValueError, 'claim source'):
                publication.validate_sources([row], root)
            row.pop('utility_refutation')
            source.write_text('def x : Nat := 2\n')
            with self.assertRaisesRegex(ValueError, 'source binding'):
                publication.validate_sources([row], root)

    def test_rejected_complete_bundle_never_replaces_published_bytes(self):
        import subprocess
        import zipfile
        for damage in ['material', 'missing', 'duplicate', 'unreferenced', 'nonobject-provenance',
                       'provenance', 'attestation', 'declaration-identity', 'noncanonical',
                       'report-symlink', 'materials-symlink', 'missing-sidecar', 'missing-origin',
                       'origin-compatibility', 'origin-report', 'origin-executable', 'legacy-provenance',
                       'bad-sha256', 'illegal-mode']:
            with self.subTest(damage=damage), tempfile.TemporaryDirectory() as directory:
                directory = Path(directory)
                spool = directory / 'spool'
                spool.mkdir()
                (spool / '0.statement').write_text('statement-v1(λ😀)')
                declaration = dict(axioms=[], include_in_statement=False, kind='opaque',
                    material_file='0.statement', name='x', name_key='ns(n0,1:x)')
                raw = dict(schema=materials.SPOOL_SCHEMA, modules=[dict(module='X', source_path='X.lean',
                    source_sha256='sha256:' + 'a' * 64, imports=[], declarations=[declaration])])
                source = directory / 'spool.json'
                source.write_text(json.dumps(raw))
                report = directory / 'report.json'
                materials.compact(source, spool, report)
                helper = Path(publication.__file__).resolve().parent.parent / 'scripts/report/lean-report-input.sh'
                pair, repository = subprocess.check_output([str(helper), 'coordinates', 'b'*64, 'b'*64, 'c'*64, 'd'*64], text=True).split()
                coordinates = dict(repository=repository, producer='b'*64, sources='c'*64, config='d'*64, input=pair)
                origins = {'X': dict(module='X', report_sha256=publication.digest(report),
                    compatibility_sha256='b'*64, producer_sources_sha256='e'*64, inspector_executable_sha256='f'*64,
                    input_sources={'X.lean': 'a'*64})}
                publication.write_sidecars(report, coordinates, origins)
                live = directory / 'live.json'
                publication.publish(report, live, coordinates)
                before = {suffix: publication.member(live, suffix).read_bytes() for suffix in publication.SUFFIXES}
                if damage in ['material', 'missing', 'duplicate', 'unreferenced']:
                    path = publication.member(report, '.materials.zip')
                    with zipfile.ZipFile(path) as archive:
                        entries = [(name, archive.read(name)) for name in archive.namelist()]
                    if damage == 'material': entries[0] = (entries[0][0], b'different valid UTF-8')
                    if damage == 'missing': entries = []
                    if damage == 'duplicate': entries += entries
                    if damage == 'unreferenced': entries.append(('sha256/' + 'f'*64, b'extra'))
                    with zipfile.ZipFile(path, 'w') as archive:
                        for name, data in entries: archive.writestr(name, data)
                elif damage == 'nonobject-provenance':
                    publication.member(report, '.provenance.json').write_text('[]')
                elif damage == 'provenance':
                    value = json.loads(publication.member(report, '.provenance.json').read_text())
                    value['producer_sha256'] = 'f'*64
                    publication.member(report, '.provenance.json').write_text(json.dumps(value))
                elif damage in ['missing-origin', 'origin-compatibility', 'origin-report', 'origin-executable', 'legacy-provenance']:
                    path = publication.member(report, '.provenance.json')
                    value = json.loads(path.read_text())
                    if damage == 'missing-origin': value['module_origins'].clear()
                    elif damage == 'legacy-provenance': value['schema'] = 'stratalint-lean-report-provenance-v1'
                    else:
                        field = {'origin-compatibility': 'compatibility_sha256', 'origin-report': 'report_sha256',
                                 'origin-executable': 'inspector_executable_sha256'}[damage]
                        value['module_origins']['X'][field] = 'bad' if damage == 'origin-executable' else '0' * 64
                    path.write_text(json.dumps(value))
                elif damage == 'attestation':
                    publication.member(report, '.input.attestation').write_text('malformed\n')
                elif damage == 'declaration-identity':
                    value = json.loads(report.read_text())
                    value['modules'][0]['declarations'][0]['statement_id'] = 'sha256:' + 'f'*64
                    report.write_bytes(materials.canonical_json(value))
                    publication.write_sidecars(report, coordinates, origins)
                elif damage == 'noncanonical':
                    report.write_text(json.dumps(json.loads(report.read_text())))
                    publication.write_sidecars(report, coordinates, origins)
                elif damage == 'missing-sidecar':
                    publication.member(report, '.provenance.json').unlink()
                elif damage == 'bad-sha256':
                    publication.member(report, '.sha256').write_text('0' * 64 + '  report.json\n')
                elif damage == 'illegal-mode':
                    path = publication.member(report, '.provenance.json')
                    value = json.loads(path.read_text())
                    value['mode'] = 'illegal'
                    path.write_text(json.dumps(value))
                else:
                    path = report if damage == 'report-symlink' else publication.member(report, '.materials.zip')
                    regular = path.with_name(path.name + '.regular')
                    path.rename(regular)
                    path.symlink_to(regular.name)
                with self.assertRaises((ValueError, TypeError)):
                    publication.publish(report, live, coordinates, mode='cached')
                self.assertEqual(before, {suffix: publication.member(live, suffix).read_bytes() for suffix in publication.SUFFIXES})


class EntryPointTests(unittest.TestCase):
    def test_failed_phase_preserves_public_bundle_and_propagates_exit(self):
        for phase, status, calls in [('inputs', 2, []), ('utility-input-build', 37, ['build']),
                                     ('ensure', 38, ['build', 'ensure']),
                                     ('report', 39, ['build', 'ensure', 'report']),
                                     ('publish', 40, ['build', 'ensure', 'report', 'publish'])]:
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                def write(name, text):
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(text)
                    path.chmod(0o755)
                repository = Path(publication.__file__).resolve().parents[2]
                for name in ['tools/lean-inspector/inspect.sh', 'tools/scripts/report/lean-report-selection.py']:
                    write(name, (repository / name).read_text())
                write('Trureturing.lean', 'def x : Nat := 1\n')
                paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
                write('lean-report-inputs.json', json.dumps(dict(schema_version=1, report_semantic_version=1,
                    report_modules=paths('Trureturing.lean'), inspector_sources=paths(), config_inputs=paths(),
                    producer_scopes={'lean-report': paths('lean-report-inputs.json',
                        'tools/scripts/report/lean-report-selection.py'), 'scribe-content': paths()})))
                def shell_phase(name, label, exit_code):
                    write(name, '#!/bin/sh\nprintf "%s\\n" ' + label + ' >> "$CALLS"\nexit ' + str(exit_code) + '\n')
                shell_phase('bin/dotnet', 'build', 37 if phase == 'utility-input-build' else 0)
                shell_phase('tools/scripts/worktree/lean-cache-ensure.sh', 'ensure', 38 if phase == 'ensure' else 0)
                shell_phase('bin/lake', 'report', 39 if phase == 'report' else 0)
                write('tools/scripts/worktree/lean-cache-run.sh', '#!/bin/sh\nexec "$@"\n')
                write('tools/scripts/lib/resource-observation-lib.sh', 'resource_observe() { :; }\n')
                write('tools/lean-inspector/native.py',
                    'import os\nfrom pathlib import Path\nwith Path(os.environ["CALLS"]).open("a") as out: out.write("publish\\n")\nraise SystemExit(40)\n')
                if phase == 'inputs':
                    (root / 'lean-report-inputs.json').unlink()
                report = root / 'public/report.json'
                report.parent.mkdir()
                before = {suffix: ('previous' + suffix).encode() for suffix in publication.SUFFIXES}
                for suffix, data in before.items():
                    publication.member(report, suffix).write_bytes(data)
                record = root / 'calls'
                env = dict(os.environ, PATH=str(root / 'bin') + os.pathsep + os.environ['PATH'],
                    CALLS=str(record), LAKE_BIN=str(root / 'bin/lake'), STRATALINT_INSPECTOR_SUPERVISED='1')
                result = subprocess.run(['bash', str(root / 'tools/lean-inspector/inspect.sh'),
                    '--repository', str(root), '--output', str(report)], env=env, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, status, result.stdout + result.stderr)
                self.assertIn(f'LEAN_INSPECTOR_FAILED phase={phase} exit={status}', result.stderr)
                self.assertEqual(record.read_text().splitlines() if record.exists() else [], calls)
                self.assertEqual(before, {suffix: publication.member(report, suffix).read_bytes() for suffix in publication.SUFFIXES})


if __name__ == '__main__':
    unittest.main()
