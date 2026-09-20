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
import native


def manifest_fixture(root, version=9):
    path = root / 'lean-report-inputs.json'
    if not path.exists():
        paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
        path.write_text(json.dumps(dict(schema_version=1, report_semantic_version=version,
            report_modules=paths(), inspector_sources=paths(), config_inputs=paths(),
            producer_scopes={'lean-report': paths('lean-report-inputs.json',
                'tools/scripts/report/lean-report-selection.py'), 'scribe-content': paths()})))
    return path


def evidence_fixture(manifest):
    return dict(schema_version=1,
        compatibility_version=json.loads(manifest.read_text())['report_semantic_version'],
        inventory=[], registered=[], records=[], inputs=[])


class ManifestVersionTests(unittest.TestCase):
    def test_manifest_only_bump_accepts_nine_and_rejects_eight(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = manifest_fixture(root, 9)
            evidence = evidence_fixture(manifest)
            self.assertEqual(evidence['compatibility_version'], 9)
            try:
                materials.validate_template_evidence(evidence, manifest)
            except Exception as error:
                self.fail('[FAIL] manifest_only_bump_accepts_nine: ' + str(error))
            with self.assertRaisesRegex(ValueError, 'DTR-EvidenceVersion'):
                materials.validate_template_evidence(dict(evidence, compatibility_version=8), manifest)

    def test_absent_evidence_version_uses_named_diagnostic(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = manifest_fixture(Path(directory), 9)
            evidence = evidence_fixture(manifest)
            del evidence['compatibility_version']
            with self.assertRaisesRegex(ValueError, 'DTR-EvidenceVersion',
                    msg='[FAIL] absent_evidence_version_uses_named_diagnostic'):
                materials.validate_template_evidence(evidence, manifest)

    def test_malformed_evidence_version_uses_named_diagnostic(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = manifest_fixture(Path(directory), 9)
            for version in [None, True, '9', 0, -1, 9.0, 9.5]:
                with self.subTest(version=version):
                    evidence = dict(evidence_fixture(manifest), compatibility_version=version)
                    with self.assertRaisesRegex(ValueError, 'DTR-EvidenceVersion',
                            msg='[FAIL] malformed_evidence_version_uses_named_diagnostic'):
                        materials.validate_template_evidence(evidence, manifest)

    def test_unrelated_malformed_evidence_keeps_structural_diagnostic(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = manifest_fixture(Path(directory), 9)
            valid = evidence_fixture(manifest)
            missing_inventory = dict(valid)
            del missing_inventory['inventory']
            for evidence, diagnostic in [(None, 'has unexpected fields'), ([], 'has unexpected fields'),
                    (missing_inventory, 'has unexpected fields'), (dict(valid, unknown=1), 'has unexpected fields'),
                    (dict(valid, schema_version=True), 'is malformed'), (dict(valid, inventory=None), 'is malformed')]:
                with self.subTest(evidence=evidence):
                    with self.assertRaisesRegex(ValueError,
                            '^Inspector declared-template evidence ' + diagnostic + '$'):
                        materials.validate_template_evidence(evidence, manifest)

    def test_missing_or_malformed_manifest_version_rejected(self):
        for text in [None, '{}', '{', '[]', '{"report_semantic_version":null}',
                     '{"report_semantic_version":"8"}', '{"report_semantic_version":true}',
                     '{"report_semantic_version":0}', '{"report_semantic_version":-1}',
                     '{"report_semantic_version":6.5}']:
            with self.subTest(manifest=text), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = manifest_fixture(root)
                evidence = evidence_fixture(manifest)
                if text is None:
                    manifest.unlink()
                else:
                    manifest.write_text(text)
                with self.assertRaisesRegex(ValueError, 'DTR-ManifestVersion',
                        msg='[FAIL] invalid_manifest_version_rejected'):
                    materials.validate_template_evidence(evidence, manifest)

    def test_compact_cli_uses_explicit_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = manifest_fixture(root, 9)
            spool = root / 'spool'
            spool.mkdir()
            source, output = root / 'spool.json', root / 'report.json'
            row = dict(module='X', source_path='X.lean', source_sha256='sha256:' + 'a'*64,
                imports=[], declarations=[], information_templates=evidence_fixture(manifest))
            source.write_text(json.dumps(dict(schema=materials.SPOOL_SCHEMA, modules=[row])))
            result = subprocess.run([sys.executable, materials.__file__, 'compact', str(source),
                str(spool), str(output), str(manifest)], cwd=spool, capture_output=True)
            self.assertEqual(result.returncode, 0, '[FAIL] compact_explicit_manifest: ' + result.stderr.decode())
            rows = publication.validate_rows(output, publication.member(output, '.materials.zip'), manifest=manifest)
            self.assertEqual(rows[0]['information_templates']['compatibility_version'], 9)
            row['information_templates']['compatibility_version'] = 7
            source.write_text(json.dumps(dict(schema=materials.SPOOL_SCHEMA, modules=[row])))
            result = subprocess.run([sys.executable, materials.__file__, 'compact', str(source),
                str(spool), str(output), str(manifest)], cwd=spool, capture_output=True)
            self.assertEqual(result.returncode, 1)
            self.assertIn(b'DTR-EvidenceVersion', result.stderr)


class StreamingTests(unittest.TestCase):
    def test_chunked_spool_preserves_material_bytes(self):
        data = ('λ😀' * 40000).encode()
        chunks = [data[i:i + materials.BUFFER_BYTES] for i in range(0, len(data), materials.BUFFER_BYTES)]
        wire = b'chunks\n' + b''.join(str(len(c)).encode() + b'\n' + c for c in chunks) + b'0\ndone\n'
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, materials.__file__, 'stream', directory],
                input=wire, capture_output=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, b'ok\ndone\n')
            self.assertEqual(materials.read_material(Path(directory) / '0.statement.gz'), data)

    def test_chunked_spool_rejects_incomplete_or_oversize_frame_without_output(self):
        for wire in [b'chunks\n4\nabc', b'chunks\n65537\n', b'chunks\n0\n', b'chunks\n1\nx', b'chunks\n-1\n']:
            with self.subTest(wire=wire), tempfile.TemporaryDirectory() as directory:
                result = subprocess.run([sys.executable, materials.__file__, 'stream', directory],
                    input=wire, capture_output=True, timeout=30)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(list(Path(directory).iterdir()), [])

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
                        materials.compact(report, spool, output, manifest_fixture(directory))
                self.assertFalse(output.exists())



class PublicationTests(unittest.TestCase):
    def test_pattern_cache_keeps_path_checks_live(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / (Path(directory).name + '.lean')
            path.write_text('def input := 1\n')
            inputs = object.__new__(publication.selection.Selection)
            inputs.root = Path(directory)
            compile_pattern = publication.selection.re.compile
            with patch.object(publication.selection.re, 'compile', wraps=compile_pattern) as compiler:
                for _ in range(8):
                    self.assertEqual(inputs.safe_file(path.name), path)
                self.assertEqual(compiler.call_count, 0, '[FAIL] path_checks_need_no_regex')
                for _ in range(8):
                    matcher = publication.selection.compile_glob(path.name + '*', 'fixture')
                    self.assertIsNotNone(matcher.fullmatch(path.name))
                self.assertEqual(compiler.call_count, 1, '[FAIL] pattern_cache_keeps_path_checks_live')
                path.unlink()
                with self.assertRaises(ValueError):
                    inputs.safe_file(path.name)
                target = Path(directory) / 'Target.lean'
                target.write_text('def input := 1\n')
                path.symlink_to(target)
                with self.assertRaises(ValueError):
                    inputs.safe_file(path.name)

    def test_binding_batch_scope_expanded_once(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
            (root / 'lean-report-inputs.json').write_text(json.dumps(dict(schema_version=1, report_semantic_version=4,
                report_modules=paths('X*.lean'), inspector_sources=paths(), config_inputs=paths(),
                producer_scopes={'lean-report': paths('lean-report-inputs.json',
                    'tools/scripts/report/lean-report-selection.py'), 'scribe-content': paths()})))
            policy = root / 'Policy.lean'
            policy.write_text('def driver := 1\n')
            rows, requests = {}, []
            for i in range(8):
                name = 'X' + str(i)
                source = root / (name + '.lean')
                source.write_text('def x := 1\n')
                utility = root / (name + '.json')
                utility.write_text(json.dumps(dict(source_path=source.name, utilities=[])))
                rows[name] = [dict(module=name, source_path=source.name,
                    source_sha256='sha256:' + publication.digest(source),
                    information_templates=dict(evidence_fixture(manifest_fixture(root)),
                        inputs=[dict(path=policy.name, sha256=publication.digest(policy))]))]
                requests.append(['validate', [str(root), 'module', str(root), name, str(utility), 'fixture.zip']])
            request, result = root / 'request.json', root / 'result.json'
            request.write_text(json.dumps(requests))
            # Isolate the source-binding boundary from ZIP decoding. The batch
            # loop and each row's real path/hash validator still execute.
            def validate(kind, owner, name, utility, artifact, **kwargs):
                native.row_binding(rows[name], owner, name, utility,
                    **{key: value for key, value in kwargs.items() if key == 'template_inputs'})
            with patch.object(native, 'validate', side_effect=validate), patch.object(
                    publication.selection, 'Selection', wraps=publication.selection.Selection) as selections:
                native.batch(request, result)
                self.assertEqual(json.loads(result.read_text()), [0] * len(requests))
                self.assertEqual(selections.call_count, 1, '[FAIL] binding_batch_scope_expanded_once')

    def test_binding_evidence_survives_compaction_and_native_validation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'spool').mkdir()
            evidence = evidence_fixture(manifest_fixture(root))
            raw = dict(schema=materials.SPOOL_SCHEMA, modules=[dict(module='X', source_path='X.lean',
                source_sha256='sha256:' + 'a'*64, imports=[], declarations=[], information_templates=evidence)])
            source, report = root / 'spool.json', root / 'report.json'
            source.write_text(json.dumps(raw))
            materials.compact(source, root / 'spool', report, manifest_fixture(root))
            rows = publication.validate_rows(report, publication.member(report, '.materials.zip'), manifest=manifest_fixture(root))
            self.assertEqual(rows[0]['information_templates'], evidence)
            for field, value in [('compatibility_version', 3), ('compatibility_version', 4),
                                 ('compatibility_version', 5), ('compatibility_version', 7),
                                 ('schema_version', True), ('inputs', {}), ('extra', [])]:
                with self.subTest(field=field):
                    rows[0]['information_templates'] = dict(evidence, **{field: value})
                    report.write_bytes(materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=rows)))
                    with self.assertRaisesRegex(ValueError, 'declared-template evidence'):
                        publication.validate_rows(report, publication.member(report, '.materials.zip'), manifest=manifest_fixture(root))

    def test_binding_source_revalidation_rejects_stale_and_missing_inputs(self):
        import zipfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
            (root / 'lean-report-inputs.json').write_text(json.dumps(dict(schema_version=1, report_semantic_version=4,
                report_modules=paths('X.lean'), inspector_sources=paths(), config_inputs=paths(),
                producer_scopes={'lean-report': paths('lean-report-inputs.json',
                    'tools/scripts/report/lean-report-selection.py'), 'scribe-content': paths()})))
            policy = root / 'Policy.lean'
            policy.write_text('def driver := 1\n')
            source = root / 'X.lean'
            source.write_text('def x := 1\n')
            utility = root / 'utility.json'
            utility.write_text(json.dumps(dict(source_path='X.lean', utilities=[])))
            evidence = dict(evidence_fixture(manifest_fixture(root)),
                inputs=[dict(path='Policy.lean', sha256=publication.digest(policy))])
            rows = [dict(module='X', source_path='X.lean', source_sha256='sha256:' + publication.digest(source),
                imports=[], declarations=[], information_templates=evidence)]
            inputs = publication.selection.Selection(root)
            report = root / 'report.json'
            report.write_bytes(materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=rows)))
            with zipfile.ZipFile(publication.member(report, '.materials.zip'), 'w'):
                pass
            compatibility = inputs.compatibility()
            helper = Path(publication.__file__).resolve().parent.parent / 'scripts/report/lean-report-input.sh'
            pair, repository = subprocess.check_output([str(helper), 'coordinates', compatibility,
                compatibility, 'c' * 64, 'd' * 64], text=True).split()
            coordinates = dict(repository=repository, producer=compatibility,
                sources='c' * 64, config='d' * 64, input=pair)
            origins = {'X': dict(module='X', report_sha256=publication.digest(report),
                compatibility_sha256=compatibility, producer_sources_sha256='e' * 64,
                inspector_executable_sha256='f' * 64, input_sources={'X.lean': publication.digest(source)})}
            publication.write_sidecars(report, coordinates, origins)
            validators = [lambda: native.row_binding(rows, root, 'X', utility),
                          lambda: native.row_binding(rows, root, 'X', utility, template_inputs=inputs),
                          lambda: publication.validate_template_sources(rows, root, inputs=inputs),
                          lambda: publication.validate_sources(rows, root),
                          lambda: publication.verify_inputs(report, root),
                          lambda: publication.validate_bundle(report, coordinates, root)]
            for validate in validators:
                validate()
            policy.write_text('def driver := 2\n')
            for index, validate in enumerate(validators):
                with self.subTest(validator=index, damage='changed'), self.assertRaisesRegex(
                        ValueError, 'stale declared-template input', msg='[FAIL] native_binding_input_freshness'):
                    validate()
            policy.unlink()
            for index, validate in enumerate(validators):
                with self.subTest(validator=index, damage='missing'), self.assertRaises((ValueError, OSError)):
                    validate()

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
            materials.compact(source, spool, report, manifest_fixture(root))
            verified = {}
            with patch.object(materials, 'material_identities', wraps=materials.material_identities) as identities:
                rows = publication.validate_rows(report, archive, verified, manifest=manifest_fixture(root))
                publication.validate_rows(report, archive, verified, manifest=manifest_fixture(root))
                self.assertEqual(identities.call_count, 1)
                original = report.read_bytes()
                rows[0]['declarations'][0]['statement_id'] = 'sha256:' + 'b'*64
                report.write_bytes(materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=rows)))
                with self.assertRaisesRegex(ValueError, 'identity mismatch'):
                    publication.validate_rows(report, archive, verified, manifest=manifest_fixture(root))
                report.write_bytes(original)
                with zipfile.ZipFile(archive) as reader:
                    name = reader.namelist()[0]
                with zipfile.ZipFile(archive, 'w') as writer:
                    writer.writestr(name, b'corrupt actual bytes')
                with self.assertRaisesRegex(ValueError, 'material address mismatch'):
                    publication.validate_rows(report, archive, verified, manifest=manifest_fixture(root))

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
                materials.compact(source, spool, report, manifest_fixture(directory))
                helper = Path(publication.__file__).resolve().parent.parent / 'scripts/report/lean-report-input.sh'
                pair, repository = subprocess.check_output([str(helper), 'coordinates', 'b'*64, 'b'*64, 'c'*64, 'd'*64], text=True).split()
                coordinates = dict(repository=repository, producer='b'*64, sources='c'*64, config='d'*64, input=pair)
                origins = {'X': dict(module='X', report_sha256=publication.digest(report),
                    compatibility_sha256='b'*64, producer_sources_sha256='e'*64, inspector_executable_sha256='f'*64,
                    input_sources={'X.lean': 'a'*64})}
                publication.write_sidecars(report, coordinates, origins)
                live = directory / 'live.json'
                publication.publish(report, live, coordinates, manifest=manifest_fixture(directory))
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
                    publication.publish(report, live, coordinates, mode='cached', manifest=manifest_fixture(directory))
                self.assertEqual(before, {suffix: publication.member(live, suffix).read_bytes() for suffix in publication.SUFFIXES})


class EntryPointTests(unittest.TestCase):
    def test_prebuilt_utility_producer_is_required_and_its_failure_stops_preparation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Trureturing.lean').write_text('def x : Nat := 1\n')
            loader = 'tools/scripts/report/lean-report-selection.py'
            (root / loader).parent.mkdir(parents=True)
            (root / loader).write_text(Path(native.selection.__file__).read_text())
            paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
            (root / 'lean-report-inputs.json').write_text(json.dumps(dict(schema_version=1, report_semantic_version=1,
                report_modules=paths('Trureturing.lean'), inspector_sources=paths(), config_inputs=paths(),
                producer_scopes={'lean-report': paths('lean-report-inputs.json', loader), 'scribe-content': paths()})))
            binary = root / 'candidate producer.dll'
            binary.write_bytes(b'fixture candidate producer')
            scripts = root / 'bin'
            scripts.mkdir()
            dotnet = scripts / 'dotnet'
            dotnet.write_text('#!/usr/bin/env python3\nimport json, os, sys\nfrom pathlib import Path\n'
                'Path("utility-command.json").write_text(json.dumps(sys.argv[1:]))\n'
                'print("[]")\nraise SystemExit(int(os.environ.get("UTILITY_EXIT", "0")))\n')
            dotnet.chmod(0o755)
            environment = dict(PATH=str(scripts) + os.pathsep + os.environ['PATH'],
                               STRATALINT_LEAN_PRODUCER_DLL=str(binary))
            with patch.dict(os.environ, environment), patch.object(publication, 'coordinates', return_value={}):
                native.prepare(root)
            self.assertEqual(json.loads((root / 'utility-command.json').read_text()),
                             [str(binary), 'lean-utility-input'])
            prepared = root / '.lake/build/lean-inspector/inputs/Trureturing.json'
            previous = prepared.read_bytes()
            for invalid in ('relative.dll', str(root / 'absent.dll')):
                with self.subTest(producer=invalid), patch.dict(os.environ,
                        dict(environment, STRATALINT_LEAN_PRODUCER_DLL=invalid)):
                    with self.assertRaisesRegex(ValueError, 'existing absolute path'):
                        native.prepare(root)
                self.assertEqual(prepared.read_bytes(), previous)
            with patch.dict(os.environ, dict(environment, UTILITY_EXIT='37')):
                with self.assertRaises(subprocess.CalledProcessError) as failure:
                    native.prepare(root)
            self.assertEqual(failure.exception.returncode, 37)
            self.assertEqual(prepared.read_bytes(), previous)

    def test_failed_phase_preserves_public_bundle_and_propagates_exit(self):
        cases = [('inputs', 2, [], False), ('utility-input-build', 37, ['build'], False),
                 ('ensure', 38, ['build', 'ensure'], False),
                 ('report', 39, ['build', 'ensure', 'report'], False),
                 ('publish', 40, ['build', 'ensure', 'report', 'publish'], False),
                 ('report', 39, ['ensure', 'report'], True)]
        for phase, status, calls, prebuilt in cases:
            with self.subTest(phase=phase, prebuilt=prebuilt), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                def write(name, text):
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(text)
                    path.chmod(0o755)
                repository = Path(publication.__file__).resolve().parents[2]
                for name in ['tools/lean-inspector/inspect.sh', 'tools/lean-inspector/reuse.py',
                             'tools/lean-inspector/materials.py', 'tools/lean-inspector/publication.py',
                             'tools/scripts/report/lean-report-selection.py']:
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
                write('candidate producer.dll', 'fixture candidate producer')
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
                    CALLS=str(record), LAKE_BIN=str(root / 'bin/lake'), STRATALINT_INSPECTOR_SUPERVISED='1',
                    STRATALINT_LEAN_PRODUCER_DLL=str(root / 'candidate producer.dll') if prebuilt else '')
                result = subprocess.run(['bash', str(root / 'tools/lean-inspector/inspect.sh'),
                    '--repository', str(root), '--output', str(report)], env=env, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, status, result.stdout + result.stderr)
                self.assertIn(f'LEAN_INSPECTOR_FAILED phase={phase} exit={status}', result.stderr)
                self.assertEqual(record.read_text().splitlines() if record.exists() else [], calls)
                self.assertEqual(before, {suffix: publication.member(report, suffix).read_bytes() for suffix in publication.SUFFIXES})


if __name__ == '__main__':
    unittest.main()
