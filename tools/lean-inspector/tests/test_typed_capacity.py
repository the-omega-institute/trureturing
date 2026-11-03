"""Production typed assessment, including its cross-process generated index.

Run after the canonical compiled-judge build. The private native fixture supplies
publication inputs; all compiled contracts and the Inspector are unmodified.
"""
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import unittest
from unittest.mock import patch
import zipfile

from test_native_support import NativeTestSupport, ROOT, publication, materials
import native

PREFIX = 'LeanInformationAuditRegTests.NativeCapacity.'


class TypedCapacityTests(NativeTestSupport, unittest.TestCase):
    def setUp(self):
        super().setUp()
        self.executable = ROOT / '.lake/build/lean-inspector/producer/bin/reportInspector'
        self.assertTrue(self.executable.is_file(), 'run make compiled-judge-test')
        search = self.guarded_command(['lake', '-d', 'tools/lean-inspector-reg',
            'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, env=os.environ)
        self.assertEqual(search.returncode, 0, search.stderr)
        self.search = search.stdout.strip()
        # Replace the transport surrogate with the exact production source.
        self.write('tools/lean-inspector/Inspector.lean',
                   (ROOT / 'tools/lean-inspector/Inspector.lean').read_text())
        self.requests = {}
        for side in ('Source', 'Left', 'Right', 'ConflictRight', 'SharedRight'):
            path = f'tools/lean-inspector/{PREFIX.replace(".", "/")}{side}.lean'
            self.copy(path)
            if side == 'Source':
                continue
            name = PREFIX + side
            olean = ROOT / f'.lake/build/lean-inspector/reg/lib/lean/{name.replace(".", "/")}.olean'
            projection = self.root / f'.lake/build/lean-inspector/judge-inputs/{name}.json'
            projection.parent.mkdir(parents=True, exist_ok=True)
            discovery = ROOT / '.lake/build/lean-inspector/producer/bin/inputDiscovery'
            result = self.guarded_command([str(discovery), name, str(olean), str(projection)])
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(json.loads(projection.read_text())['inputs'])
            utility = self.root / f'{side}.json'
            utility.write_text(json.dumps(dict(source_path=path, utilities=[])))
            Path(str(utility) + '.sources.json').write_text('[]')
            output = self.root / f'{side}.zip'
            self.requests[side] = [str(self.root), name, str(self.root / path),
                str(utility), str(self.executable), str(output), '', '']

    def produce(self, sides, capacity, *, success=True, label):
        calls = []
        stderr = self.root / f'{label}.stderr'
        stderr.write_text('')
        original = native.run_inspector

        def execute(root, executable, arguments, request_file=None):
            index = (Path(arguments[arguments.index('--generated-index') + 1])
                     if '--generated-index' in arguments else None)
            before = json.loads(index.read_text()) if index else None
            call = dict(arguments=arguments, index_before=before)
            calls.append(call)
            try:
                original(root, executable, arguments, request_file)
                call['exit'] = 0
            except ValueError:
                call['exit'] = 1
                raise
            finally:
                call['index_after'] = json.loads(index.read_text()) if index else None

        with patch.dict(os.environ, LEAN_PATH=self.search,
                STRATALINT_NATIVE_BATCH_MODULES=str(capacity),
                STRATALINT_INSPECTOR_CHILD_STDERR=str(stderr)), \
                patch.object(native, 'run_inspector', side_effect=execute):
            if success:
                native.produce_batch([self.requests[side] for side in sides])
            else:
                with self.assertRaisesRegex(ValueError, 'raw.reader_failed:exit=1'):
                    native.produce_batch([self.requests[side] for side in sides])
        self.record_result(label, dict(capacity=capacity, expected_success=success,
            calls=calls, stderr=stderr.read_text()), [stderr])
        return calls, stderr.read_text()

    def artifacts(self, sides, label):
        result = {}
        paths = []
        for side in sides:
            artifact = Path(self.requests[side][5])
            paths.append(artifact)
            with zipfile.ZipFile(artifact) as archive:
                report = archive.read(publication.RAW)
                row = json.loads(report)['modules'][0]
                evidence = row['information_templates']
                self.assertTrue(evidence['records'], 'production assessment must produce bindings')
                self.assertEqual({record['state'] for record in evidence['records']},
                                 {'declared_validated'})
                self.assertEqual({record['bridge_kind'] for record in evidence['records']},
                                 {'source-equivalence'})
                material_bytes = archive.read(publication.RAW + '.materials.zip')
            import io
            with zipfile.ZipFile(io.BytesIO(material_bytes)) as archive:
                digests = {name: hashlib.sha256(archive.read(name)).hexdigest()
                           for name in archive.namelist()}
            result[side] = dict(report=hashlib.sha256(report).hexdigest(),
                materials=hashlib.sha256(material_bytes).hexdigest(), content=digests)
        # Complete reports and material archives remain independently inspectable.
        self.record_result(label, result, paths)
        return result

    def test_typed_generated_identity_and_publication(self):
        # Every disjoint source-bound target is valid independently.
        for side in ('Left', 'Right', 'ConflictRight'):
            self.produce([side], 100, label=f'alone-{side}')
            self.artifacts([side], f'alone-{side}-artifacts')
        for sides, control in [(['Left', 'Right'], 'distinct'),
                               (['Left', 'SharedRight'], 'shared-owner')]:
            baseline = None
            for capacity in (100, 1):
                label = f'{control}-{capacity}'
                calls, _ = self.produce(sides, capacity, label=label)
                actual = self.artifacts(sides, label + '-artifacts')
                if baseline is None:
                    baseline = actual
                else:
                    self.assertEqual(actual, baseline)
                    capped = [call for call in calls if call['index_before'] is not None]
                    self.assertEqual(len(capped), 2)
                    self.assertTrue(capped[0]['index_after'])
                    self.assertEqual(capped[1]['index_before'], capped[0]['index_after'])
        for capacity in (100, 1):
            previous = {side: Path(self.requests[side][5]).read_bytes()
                        for side in ('Left', 'ConflictRight')}
            calls, diagnostic = self.produce(['Left', 'ConflictRight'], capacity,
                success=False, label=f'collision-{capacity}')
            self.assertIn('incomplete_closure:dtr.generated_target:NativeCapacity.shared', diagnostic)
            self.assertEqual({side: Path(self.requests[side][5]).read_bytes() for side in previous}, previous)
            self.record_result(f'collision-{capacity}-publication', dict(
                before={side: hashlib.sha256(data).hexdigest() for side, data in previous.items()},
                after={side: hashlib.sha256(Path(self.requests[side][5]).read_bytes()).hexdigest()
                       for side in previous}), [Path(self.requests[side][5]) for side in previous])
            if capacity == 1:
                capped = [call for call in calls if call['index_before'] is not None]
                self.assertEqual([call['exit'] for call in capped], [0, 1])
                self.assertTrue(capped[0]['index_after'])
                self.assertEqual(capped[1]['index_before'], capped[0]['index_after'])
                self.assertEqual(capped[1]['index_after'], capped[1]['index_before'])
            self.assertFalse(list((self.root / '.lake/build/lean-inspector').glob('.partition.*')))


if __name__ == '__main__':
    unittest.main()
