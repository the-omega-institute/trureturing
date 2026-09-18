"""Execute native Lake facets in private pinned-toolchain fixture packages."""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import zipfile
import zlib

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
ROOT = Path(os.environ.get('STRATALINT_NATIVE_SOURCE_ROOT', ROOT)).resolve()
sys.path.insert(0, str(HERE))
import publication
import materials
import native



from test_native_support import *

class NativeInvalidationTests:
    def test_native_config_options_rebuild_and_fail_closed(self):
        # Origin evidence includes the actual executable hash. Inspector embeds
        # its source-adjacent fallback writer path, so both builds must compile
        # in this fixture instead of mixing a cross-directory compiler seed
        # with a local rebuild. Keep optional artifact restoration off throughout.
        self.compiler_seed = None
        self.env['LAKE_ARTIFACT_CACHE'] = 'false'
        self.write('D5/Alone.lean', 'import Lean\nopen Lean Elab Term\n'
            'elab "optionType" : term => return mkConst '
            '(if (← getOptions).getBool `pp.universes false then `Bool else `Nat)\n'
            'def optionValue : optionType := default\n'
            'def inferred (x : α) := x\n')
        config = (self.root / 'lakefile.toml').read_text()
        self.build()
        before = self.stamps()
        original = self.report()[0]
        # Lake must apply actual Lean options before accepting cached rows.
        self.write('lakefile.toml', 'leanOptions.autoImplicit = false\n' + config)
        rejected = self.build(success=False)
        self.assertIn('Unknown identifier', rejected.stdout + rejected.stderr)
        self.assertEqual(before, self.stamps())
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')

        self.write('lakefile.toml', 'leanOptions.pp.universes = true\n' + config)
        self.build()
        warm = self.report()[0]
        changed = {name for name, stamp in self.stamps().items() if stamp != before[name]}
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertIn('D5.Alone', changed)
        self.assertEqual(sum(r['count'] for r in records if r['kind'] == 'extract'), len(changed))
        self.assertEqual(sum(r['count'] for r in records if r['kind'] == 'aggregate'), 1)
        def option_type(rows):
            row = next(row for row in rows if row['module'] == 'D5.Alone')
            return next(decl['type_sha256'] for decl in row['declarations'] if decl['name'] == 'optionValue')
        self.assertNotEqual(option_type(original), option_type(warm))
        self.publish()
        published = {suffix: publication.member(self.root / 'public.json', suffix).read_bytes()
                     for suffix in publication.SUFFIXES}
        executable = self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'
        producer = publication.digest(executable)
        self.record_result('config-options-warm', dict(inspector_executable_sha256=producer),
            [publication.member(self.root / 'public.json', suffix) for suffix in publication.SUFFIXES])
        stamps = self.stamps()
        self.build()
        self.assertEqual(stamps, self.stamps())
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')

        # Recompile and extract under the same option environment with no
        # optional artifact restoration; all five canonical materials agree.
        shutil.rmtree(self.root / '.lake/build')
        rebuilt = self.build()
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        extracted = sum(r['count'] for r in records if r['kind'] == 'extract')
        compiled = [name for name in sorted(stamps) if f'Built {name} (' in rebuilt.stdout + rebuilt.stderr]
        self.assertEqual(compiled, sorted(stamps))
        self.assertEqual(extracted, len(stamps))
        self.assertEqual(publication.digest(executable), producer)
        self.publish()
        fresh = {suffix: publication.member(self.root / 'public.json', suffix).read_bytes()
                 for suffix in publication.SUFFIXES}
        result = dict(changed=sorted(changed), original_type=option_type(original),
            current_type=option_type(warm), warm_matches_fresh=published == fresh,
            rejected_exit_code=rejected.returncode, compiled_modules=compiled,
            extracted=extracted, inspector_executable_sha256=producer)
        self.record_result('config-options', result,
            [publication.member(self.root / 'public.json', suffix) for suffix in publication.SUFFIXES])
        self.assertEqual(published, fresh)

    def test_native_invalidation(self):
        self.build()
        rows, original_report, original_materials = self.report()
        self.assertEqual(len(rows), 4)
        self.assertTrue(rows[-1]['utility_refutation']['is_closed_negation'])
        self.assertTrue((self.root / '.lake/build/lib/lean/Audit.olean').is_file())
        self.assertTrue(list((self.root / '.lake/build/lib').glob('*Audit*.a')))
        self.assertTrue((self.root / '.lake/build/lib/lean/External.olean').is_file())
        self.assertTrue((self.root / '.lake/build/lib/lean/D5/B.olean.private').is_file())
        self.check_census_modes(rows)
        before = self.stamps()
        self.build()
        self.assertEqual(before, self.stamps(), 'unchanged build extracted rows')
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.assertEqual(self.report()[1:], (original_report, original_materials))

        def changed(expected):
            nonlocal before
            self.build()
            after = self.stamps()
            actual = {name for name in after if after[name] != before.get(name)}
            self.assertEqual(actual, set(expected))
            before = after
            records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
            self.assertEqual(sum(r['count'] for r in records if r['kind'] == 'extract'), len(expected))

        self.write('D5/B.lean', (self.root / 'D5/B.lean').read_text().replace(':= 1', ':= 2'))
        changed(['D5.B', 'D5.A', 'Fixture'])
        self.write('D5/Alone.lean', (self.root / 'D5/Alone.lean').read_text() + '-- raw source bytes\n')
        changed(['D5.Alone'])
        self.write('ClaimSupport.lean', 'def claimSupport : Prop := True\n')
        changed(['Fixture'])
        self.assertFalse(self.report()[0][-1]['utility_refutation']['is_closed_negation'])
        self.write('External.lean', 'def claim : Prop := True\n')
        self.utility()
        changed(['Fixture'])
        self.assertFalse(self.report()[0][-1]['utility_refutation']['is_closed_negation'])
        self.utility('absent')
        changed(['Fixture'])
        self.write('D5/Added.lean', 'def added : Nat := 3\n')
        changed(['D5.Added'])
        (self.root / 'D5/Added.lean').unlink()
        self.build()
        self.assertNotIn('D5.Added', [row['module'] for row in self.report()[0]])
        self.write('Audit.lean', 'def audit : Nat := 2\n')
        changed([])
        # The fixed injected driver also governs modules with no registry import.
        self.write('LeanInformationAudit/Registry.lean', 'def fixtureDriver : Nat := 2\n')
        changed(['D5.B', 'D5.A', 'D5.Alone', 'Fixture'])
    def test_reported_module_proof_axioms_invalidate_public_trace(self):
        # Both registered modules use module headers. The public theorem body
        # in B is not exposed to A's ordinary public import, but Inspector reads
        # it through Lean's private import mode when computing A's axioms.
        self.write('D5/A.lean', 'module\npublic import D5.B\npublic section\n'
            'theorem value : True := D5.support\n')
        support = 'module\npublic section\nnamespace D5\ntheorem support : True := True.intro\n'
        self.write('D5/B.lean', support)

        def snapshot(phase):
            rows, report, material = self.report()
            artifacts = list((self.root / '.lake/build/lean-inspector/modules').glob('*.zip'))
            artifacts += [self.root / '.lake/build/lean-inspector/report.zip']
            artifacts += [self.root / f'.lake/build/lib/lean/D5/{name}.olean{suffix}'
                          for name in ['A', 'B'] for suffix in ['', '.server', '.private']]
            artifacts += [self.root / path for path in ['D5/A.lean', 'D5/B.lean', 'activity.jsonl']]
            data = dict(rows=rows, origins=self.origins(),
                artifacts={str(p.relative_to(self.root)): publication.digest(p) for p in artifacts},
                activity=[json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()])
            self.record_result(phase, data, artifacts)
            return data, report, material

        self.build()
        before, _, _ = snapshot('before')
        stamps = self.stamps()
        self.build()
        self.assertEqual(stamps, self.stamps())
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.write('D5/B.lean', support.replace('True.intro',
            'Classical.choice (show Nonempty True from ⟨True.intro⟩)'))
        self.build()
        warm, warm_report, warm_material = snapshot('warm')
        changed = {name for name, stamp in self.stamps().items() if stamp != stamps[name]}
        # Force clean report extraction through the same native owner, retaining
        # compiled Lean inputs and disabling restoration from the fixture cache.
        state = self.root / '.lake/build/lean-inspector'
        for path in [*(state / 'modules').glob('*.zip*'), *state.glob('report.zip*')]:
            path.unlink()
        self.env['LAKE_ARTIFACT_CACHE'] = 'false'
        self.build()
        clean, clean_report, clean_material = snapshot('clean')

        def declaration(data, module, name):
            row = next(row for row in data['rows'] if row['module'] == module)
            return next(decl for decl in row['declarations'] if decl['name'] == name)

        public = '.lake/build/lib/lean/D5/B.olean'
        private = public + '.private'
        result = dict(changed=sorted(changed),
            public_olean_changed=before['artifacts'][public] != warm['artifacts'][public],
            private_olean_changed=before['artifacts'][private] != warm['artifacts'][private],
            theorem_type_preserved=declaration(before, 'D5.B', 'D5.support')['type_sha256'] ==
                declaration(warm, 'D5.B', 'D5.support')['type_sha256'],
            extracted={phase: sum(r['count'] for r in data['activity'] if r['kind'] == 'extract')
                       for phase, data in [('before', before), ('warm', warm), ('clean', clean)]},
            axioms={phase: {name: declaration(data, module, name)['axioms']
                           for module, name in [('D5.A', 'value'), ('D5.B', 'D5.support')]}
                    for phase, data in [('before', before), ('warm', warm), ('clean', clean)]},
            warm_matches_clean=warm_report == clean_report and warm_material == clean_material,
            unaffected_origin_preserved=before['origins']['D5.Alone'] == warm['origins']['D5.Alone'])
        self.record_result('comparison', result)
        self.assertEqual(result['axioms']['before'], {'value': [], 'D5.support': []})
        self.assertEqual(result['axioms']['clean'],
                         {'value': ['Classical.choice'], 'D5.support': ['Classical.choice']})
        # Pinned Lean exports axiom dependencies in exportedAxiomsExt even when
        # the theorem body is hidden. An axiom-changing proof edit therefore
        # changes the public olean and reaches ordinary module importers.
        self.assertTrue(result['public_olean_changed'])
        self.assertTrue(result['private_olean_changed'])
        self.assertTrue(result['theorem_type_preserved'])
        self.assertTrue(result['warm_matches_clean'], json.dumps(result))
        self.assertEqual(changed, {'D5.A', 'D5.B', 'Fixture'})
        self.assertEqual(result['extracted'], {'before': 4, 'warm': 3, 'clean': 4})
        self.assertTrue(result['unaffected_origin_preserved'])
    def test_private_transitive_definition_invalidates_utility(self):
        # Public imports hide B's definition body from A and Fixture, while
        # Inspector's private imports and transparency .all can unfold it.
        support = 'module\npublic section\nnamespace D5\ndef hidden : Prop := False\n'
        self.write('D5/B.lean', support)
        self.write('D5/A.lean', 'module\npublic import D5.B\npublic def claim : Prop := D5.hidden\n')
        self.write('Fixture.lean', 'module\npublic import D5.A\npublic theorem result : ¬ False := fun h => h\n')
        self.write('utility.json', json.dumps([dict(modulePath='Fixture.lean',
            claimGid='claim-gid', claimModule='D5.A', claimSelector='claim',
            claimSourcePath='D5/A.lean', claimSourceSha256='sha256:' + publication.digest(self.root / 'D5/A.lean'),
            resultGid='result-gid', resultModule='Fixture', resultSelector='result')]))

        def snapshot(phase):
            rows, report, material = self.report()
            artifacts = list((self.root / '.lake/build/lean-inspector/modules').glob('*.zip'))
            artifacts += [self.root / '.lake/build/lean-inspector/report.zip']
            artifacts += [self.root / f'.lake/build/lib/lean/D5/B.olean{suffix}'
                          for suffix in ['', '.server', '.private']]
            artifacts += [self.root / path for path in
                          ['D5/B.lean', 'D5/A.lean', 'Fixture.lean', 'utility.json']]
            records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
            data = dict(rows=rows, origins=self.origins(),
                artifacts={str(p.relative_to(self.root)): publication.digest(p) for p in artifacts},
                report_sha256=hashlib.sha256(report).hexdigest(),
                materials_sha256=hashlib.sha256(material).hexdigest(),
                extracted=sum(r['count'] for r in records if r['kind'] == 'extract'),
                aggregated=sum(r['count'] for r in records if r['kind'] == 'aggregate'))
            self.record_result(phase, data, artifacts)
            return data, report, material

        def evidence(rows):
            return next(row['utility_refutation']['is_closed_negation']
                        for row in rows if row['module'] == 'Fixture')

        self.build()
        before, before_report, before_material = snapshot('before')
        self.publish()
        stamps = self.stamps()
        self.build()
        unchanged, unchanged_report, unchanged_material = snapshot('unchanged')
        self.assertEqual(stamps, self.stamps())
        self.assertEqual((before_report, before_material), (unchanged_report, unchanged_material))
        self.assertEqual(before['origins'], unchanged['origins'])
        self.run_lake('--no-build', 'build', ':report')
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')

        self.write('D5/B.lean', support.replace(':= False', ':= True'))
        self.run_lake('--no-build', 'build', ':report', success=False)
        self.assertEqual(stamps, self.stamps())
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.build()
        warm, warm_report, warm_material = snapshot('warm')
        changed = {name for name, stamp in self.stamps().items() if stamp != stamps[name]}
        self.publish()
        published = json.loads((self.root / 'public.json').read_text())
        published_evidence = evidence(published['modules'])
        warm_stamps = self.stamps()
        self.build()
        self.assertEqual(warm_stamps, self.stamps())
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.assertEqual(warm['origins'], self.origins())

        # Clean report extraction uses the same native owner and compiled
        # inputs, with optional artifact restoration disabled in this fixture.
        state = self.root / '.lake/build/lean-inspector'
        for path in [*(state / 'modules').glob('*.zip*'), *state.glob('report.zip*')]:
            path.unlink()
        self.env['LAKE_ARTIFACT_CACHE'] = 'false'
        self.build()
        clean, clean_report, clean_material = snapshot('clean')
        self.publish()
        public = '.lake/build/lib/lean/D5/B.olean'
        result = dict(changed=sorted(changed),
            public_olean_changed=before['artifacts'][public] != warm['artifacts'][public],
            private_olean_changed=before['artifacts'][public + '.private'] != warm['artifacts'][public + '.private'],
            evidence={phase: evidence(data['rows']) for phase, data in
                      [('before', before), ('unchanged', unchanged), ('warm', warm), ('clean', clean)]},
            extracted={phase: data['extracted'] for phase, data in
                       [('before', before), ('unchanged', unchanged), ('warm', warm), ('clean', clean)]},
            aggregated={phase: data['aggregated'] for phase, data in
                        [('before', before), ('unchanged', unchanged), ('warm', warm), ('clean', clean)]},
            warm_matches_clean=warm_report == clean_report and warm_material == clean_material,
            unaffected_origin_preserved=before['origins']['D5.Alone'] == warm['origins']['D5.Alone'],
            published_closed_negation=published_evidence,
            publication_and_current_input_verification_passed=True)
        self.record_result('comparison', result)
        self.assertFalse(result['public_olean_changed'])
        self.assertTrue(result['private_olean_changed'])
        self.assertEqual(result['evidence'], {'before': True, 'unchanged': True, 'warm': False, 'clean': False})
        self.assertFalse(published_evidence)
        self.assertTrue(result['warm_matches_clean'], json.dumps(result))
        self.assertEqual(changed, {'D5.A', 'D5.B', 'Fixture'})
        self.assertEqual(result['extracted'], {'before': 4, 'unchanged': 0, 'warm': 3, 'clean': 4})
        self.assertEqual(result['aggregated'], {'before': 1, 'unchanged': 0, 'warm': 1, 'clean': 1})
        self.assertTrue(result['unaffected_origin_preserved'])
    def test_exported_transitive_dependency_binding(self):
        self.build()
        self.publish()
        before = self.report()[0][-1]['utility_refutation']['is_closed_negation']
        dependency = self.root / 'ClaimSupport.lean'
        old_sha = publication.digest(dependency)
        coordinates = publication.coordinates(self.root)
        self.write('ClaimSupport.lean', 'def claimSupport : Prop := True\n')
        stage = subprocess.run([sys.executable, str(self.root / 'tools/lean-inspector/publication.py'),
            'stage', '--bundle', str(self.root / 'public.json'), '--repository', str(self.root),
            '--staging-directory', str(self.root / 'staged')], env=self.env,
            text=True, capture_output=True, timeout=120)
        verify = subprocess.run(['bash', str(self.root / 'tools/scripts/report/lean-report-input.sh'),
            'verify', '--repository', str(self.root), '--report', str(self.root / 'public.json')],
            env=self.env, text=True, capture_output=True, timeout=120)
        self.build()
        after = self.report()[0][-1]['utility_refutation']['is_closed_negation']
        result = dict(lean_generated=True, dependency='ClaimSupport.lean',
            dependency_sha256_before=old_sha, dependency_sha256_after=publication.digest(dependency),
            coordinates_unchanged=coordinates == publication.coordinates(self.root),
            old_closed_negation=before, new_closed_negation=after,
            stage_exit=stage.returncode, stage_stderr=stage.stderr,
            verify_exit=verify.returncode, verify_stderr=verify.stderr)
        if output := os.environ.get('STRATALINT_DEPENDENCY_PROBE_RESULT'):
            Path(output).write_text(json.dumps(result, indent=2) + '\n')
        self.assertTrue(before)
        self.assertFalse(after, 'mutation must change actual Lean-generated semantic evidence')
        self.assertNotEqual(stage.returncode, 0, json.dumps(result))
        self.assertNotEqual(verify.returncode, 0, json.dumps(result))
    def test_exported_private_dependency_and_missing_binding(self):
        support = 'module\npublic section\nnoncomputable section\nprivate axiom privateInput : Nat\ndef support : Nat := privateInput\n'
        self.write('Support.lean', support)
        self.write('D5/A.lean', 'import Support\nnoncomputable def value : Nat := support\n')
        self.write('lakefile.toml', (self.root / 'lakefile.toml').read_text() + '\n[[lean_lib]]\nname = "Support"\n')
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        rejected = self.build(success=False)  # Native dependencies never invent registration.
        self.assertIn('unregistered native dependency sources: Support.lean', rejected.stdout + rejected.stderr)
        policy['dependency_sources']['include'].append(dict(pattern='Support.lean', optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()
        self.publish()
        old = self.report()[0][0]['declarations'][0]['axioms']
        self.assertTrue(any('privateInput' in name for name in old))
        self.write('Support.lean', support.replace('axiom privateInput : Nat', 'def privateInput : Nat := 3'))
        with self.assertRaisesRegex(ValueError, 'stale dependency'):
            publication.validate_bundle(self.root / 'public.json', publication.coordinates(self.root), self.root)
        self.build()
        self.assertEqual(self.report()[0][0]['declarations'][0]['axioms'], [])
        self.publish()
        # Simulate pre-binding row and aggregate sidecars. Never manufacture
        # evidence for old bytes from the current dependency snapshot.
        before = self.stamps()
        expected = self.report()[1:]
        for relative in [*(f'modules/{name}.zip' for name in before), 'report.zip']:
            artifact = self.root / '.lake/build/lean-inspector' / relative
            with zipfile.ZipFile(artifact) as archive:
                entries = [(info, archive.read(info)) for info in archive.infolist()]
            artifact.unlink()
            with zipfile.ZipFile(artifact, 'w') as archive:
                for info, data in entries:
                    if info.filename.endswith('.provenance.json'):
                        origin = json.loads(data)
                        records = origin['module_origins'].values() if 'module_origins' in origin else [origin]
                        for record in records:
                            record.pop('input_sources')
                        data = json.dumps(origin).encode()
                    archive.writestr(info, data)
        result = subprocess.run([sys.executable, str(self.root / 'tools/lean-inspector/native.py'),
            'publish', str(self.root), str(self.root / 'rejected.json')], env=self.env, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.root / 'rejected.json').exists())
        self.build()
        self.assertEqual({name for name, value in self.stamps().items() if value != before[name]}, set(before))
        self.assertEqual(expected, self.report()[1:])
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual([row['count'] for row in records if row['kind'] == 'extract'], [len(before)])
        self.publish()
        self.build()
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '',
                         'successfully reconstructed legacy artifacts must be reusable')
