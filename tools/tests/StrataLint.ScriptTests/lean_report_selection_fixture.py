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
    return dict(schema_version=1,
        report_modules=dict(include=[spec('Trureturing.lean'), spec('D5/**/*.lean', True)], exclude=[]),
        inspector_sources=dict(include=[spec('tools/lean-inspector/**/*.lean', True)], exclude=[]),
        config_inputs=paths('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'),
        producer_scopes={
            'lean-report': paths(MANIFEST, LOADER, INPUT, 'tools/lean-inspector/inspect.sh',
                'tools/lean-inspector/delta.py', 'tools/lean-inspector/materials.py', 'Engine/**/*.cs'),
            'scribe-content': dict(include=[spec('Blueprint/**/*.scribe.cs', True)], exclude=[])},
        impact_cohorts=[
            dict(id='root', members=['Trureturing.lean'], exclude=[], depends_on=['consumer', 'alone']),
            dict(id='base', members=['D5/Base*.lean'], exclude=[], depends_on=[]),
            dict(id='claim', members=['D5/Claim*.lean'], exclude=[], depends_on=['base']),
            # Refutation references a non-imported claim, by authored policy.
            dict(id='consumer', members=['D5/Consumer*.lean'], exclude=[], depends_on=['claim']),
            dict(id='alone', members=['D5/Alone*.lean'], exclude=[], depends_on=[])])


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
                'Blueprint/Probe.scribe.cs': '// document\n'}.items():
            self.write(path, text)
        for relative in (LOADER, INPUT, 'tools/scripts/worktree/lean-cache-input.sh',
                'tools/lean-inspector/inspect.sh', 'tools/lean-inspector/delta.py',
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
            ('missing-group', lambda p: p['impact_cohorts'][0]['depends_on'].append('missing-group')),
            ('base', lambda p: p['impact_cohorts'].append(copy.deepcopy(p['impact_cohorts'][1]))),
            ('D5/Base.lean', lambda p: p['impact_cohorts'][1].update(members=['D5/Uncovered*.lean'])),
            ('D5/Base.lean', lambda p: p['impact_cohorts'][2]['members'].append('D5/Base*.lean')),
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

    def test_cohort_changes(self):
        selected = self.selection()
        current = selected.modules()
        self.assertEqual(selected.affected(['D5/Base.lean'], current),
            ['D5.Base', 'D5.Claim', 'D5.Consumer', 'Trureturing'])
        self.assertEqual(selected.affected(['D5/Claim.lean'], current),
            ['D5.Claim', 'D5.Consumer', 'Trureturing'])
        self.assertEqual(selected.affected(['D5/ConsumerOld.lean', 'D5/Consumer.lean'], current),
            ['D5.Consumer', 'Trureturing'])
        with self.assertRaisesRegex(ValueError, 'D5/UnknownRemoved.lean'):
            selected.affected(['D5/UnknownRemoved.lean'], current)
        # Coarsening can introduce cycles even when Lean imports are acyclic.
        self.policy['impact_cohorts'][1]['depends_on'] = ['consumer']
        self.assertEqual(self.selection().affected(['D5/Claim.lean'], current),
            ['D5.Base', 'D5.Claim', 'D5.Consumer', 'Trureturing'])

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
        self.policy['impact_cohorts'][4]['depends_on'].append('base')
        policy = self.address()
        self.assertNotEqual(renamed[1], policy[1])
        self.assertEqual(renamed[2:], policy[2:])
        self.write('Engine/Main.cs', '// producer changed')
        producer = self.address()
        self.assertNotEqual(policy[1], producer[1])
        self.write('lean-toolchain', 'changed pin')
        config = self.address()
        self.assertNotEqual(producer[3], config[3])
        self.assertEqual(producer[2], config[2])

    def test_failure_before_build(self):
        # Inherited coordinates must not bypass declaration validation.
        marker = self.repo / 'build-called'
        lake = self.repo / 'lake'
        lake.write_text('#!/bin/sh\ntouch "' + str(marker) + '"\nexit 71\n')
        lake.chmod(0o700)
        self.write('tools/scripts/worktree/lean-cache-run.sh', '#!/bin/sh\nexec "$@"\n')
        (self.repo / 'tools/scripts/worktree/lean-cache-run.sh').chmod(0o700)
        (self.repo / INPUT).chmod(0o700)
        env = dict(os.environ, TMPDIR=str(SCRATCH), LAKE_BIN=str(lake))
        for suffix in ('INPUT_ADDRESS', 'REPOSITORY_SHA256', 'PRODUCER_SHA256', 'RESIDENT_SHA256', 'CONFIG_SHA256'):
            env['STRATALINT_REPORT_' + suffix] = 'a' * 64
        for failure in ('missing-owner', 'conflicting-owner', 'missing-manifest'):
            with self.subTest(failure=failure):
                self.policy = declaration()
                if failure == 'missing-owner':
                    self.policy['impact_cohorts'][1]['members'] = ['D5/Uncovered*.lean']
                elif failure == 'conflicting-owner':
                    self.policy['impact_cohorts'][2]['members'].append('D5/Base.lean')
                self.save()
                if failure == 'missing-manifest': (self.repo / MANIFEST).unlink()
                result = subprocess.run(['bash', str(self.repo / 'tools/lean-inspector/inspect.sh'),
                    '--repository', str(self.repo), '--output', str(self.repo / 'report.json')],
                    text=True, capture_output=True, env=env)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(MANIFEST if failure == 'missing-manifest' else 'D5/Base.lean', result.stderr)
                self.assertFalse(marker.exists(), result.stdout + result.stderr)
                self.assertFalse((self.repo / 'report.json').exists())

    def test_entrypoint_failures(self):
        for relative in ('tools/scripts/report/lean-report-cache.sh',
                'tools/scripts/report/lean-report-cache.py', 'tools/scripts/report/lean-report-ci-baseline.sh',
                'tools/scripts/lean-report-pair.sh', 'tools/scripts/report/report-consumer.sh'):
            self.write(relative, (ROOT / relative).read_text())
        marker = self.repo / 'external-called'
        stub = '#!/bin/sh\ntouch "' + str(marker) + '"\nexit 71\n'
        for relative in ('bin/find', 'bin/dotnet', 'bin/gh', 'bin/lake',
                'tools/scripts/worktree/lean-cache-ensure.sh', 'tools/scripts/report/report-supervisor.sh'):
            self.write(relative, stub)
            (self.repo / relative).chmod(0o700)
        for relative in (INPUT, 'tools/lean-inspector/inspect.sh'):
            (self.repo / relative).chmod(0o700)
        env = dict(os.environ, TMPDIR=str(SCRATCH), PATH=str(self.repo / 'bin') + ':' + os.environ['PATH'],
            STRATALINT_REPORT_CACHE_ROOT=str(self.repo / 'report-cache'),
            STRATALINT_LEAN_INPUT_MEMO_ROOT=str(SCRATCH / 'memo'))
        def invoke(relative, *args):
            return subprocess.run(['bash', str(self.repo / relative), *args],
                env=env, cwd=SCRATCH, text=True, capture_output=True)
        for command in ('address', 'modules', 'producer-paths', 'scribe-producer-paths'):
            result = invoke(INPUT, command, '--repository', str(self.repo))
            self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(marker.exists())
        report = self.repo / 'report.json'
        for suffix in ('', '.sha256', '.input.attestation', '.provenance.json', '.materials.zip'):
            Path(str(report) + suffix).write_text('{}\n')
        (self.repo / MANIFEST).unlink()
        commands = [
            (INPUT, ['verify', '--repository', str(self.repo), '--report', str(report)]),
            ('tools/scripts/report/lean-report-cache.sh', ['fetch', '--repository', str(self.repo)]),
            ('tools/scripts/lean-report-pair.sh', ['--producer', str(self.repo / 'tools/lean-inspector/inspect.sh'),
                '--lake-bin', str(self.repo / 'bin/lake'), '--candidate-root', str(self.repo),
                '--candidate-output', str(self.repo / 'out.json')]),
            ('tools/scripts/report/report-consumer.sh', ['--role', 'fixture', '--report', str(report),
                '--', str(self.repo / 'bin/dotnet')])]
        for relative, args in commands:
            with self.subTest(entrypoint=relative):
                result = invoke(relative, *args)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertIn(MANIFEST, result.stderr)
                self.assertFalse(marker.exists(), result.stdout + result.stderr)

    def test_planner_changes(self):
        module_spec = importlib.util.spec_from_file_location('delta', self.repo / 'tools/lean-inspector/delta.py')
        delta = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(delta)
        selected = self.selection()
        current = selected.modules()
        old_records = [dict(module=name, source_path=path,
            source_sha256='sha256:' + hashlib.sha256((self.repo / path).read_bytes()).hexdigest(),
            imports=[], declarations=[]) for name, path in current.items()]
        # The claim consumer deliberately has no import edge. Policy owns this dependency.
        old_records[-1]['utility_refutation'] = dict(claim_source_path='D5/Claim.lean',
            claim_source_sha256=old_records[-2]['source_sha256'])
        table = self.repo / 'modules.tsv'
        output = self.repo / 'plan.json'
        cache = self.repo / 'cache'
        args = type('Args', (), dict(repository=str(self.repo), cache_root=str(cache),
            current_address='a' * 64, producer_sha='b' * 64, resident_sha='b' * 64,
            config_sha='c' * 64, module_table=str(table), plan=str(output)))()
        def run():
            table.write_text(''.join(name + '\t' + path + '\n'
                for name, path in self.loader.Selection(self.repo).modules().items()))
            delta.plan(args)
            return json.loads(output.read_text())
        self.assertEqual(run()['status'], 'fallback')  # absent optional cache
        cache.mkdir()
        entry = cache / ('d' * 64)
        entry.mkdir()
        report = entry / 'raw-lean-report.json'
        def seed(records):
            report.write_text(delta.PREFIX + ', '.join(json.dumps(r) for r in records) + delta.SUFFIX)
            digest = hashlib.sha256(report.read_bytes()).hexdigest()
            Path(str(report) + '.sha256').write_text(digest + '  raw-lean-report.json\n')
            Path(str(report) + '.input.attestation').write_text(
                'schema=stratalint-lean-report-input-attestation-v1\nrepository_input_sha256=' + 'e'*64
                + '\nproducer_sha256=' + args.producer_sha + '\nreport_sha256=' + digest + '\n')
            Path(str(report) + '.provenance.json').write_text(json.dumps(dict(
                schema='stratalint-lean-report-provenance-v1', side='candidate', mode='produced',
                source_side='candidate', input_address='sha256:' + entry.name,
                producer_sha256=args.producer_sha, repository_inspector_sha256=args.resident_sha,
                lean_config_sha256=args.config_sha, lean_sources_sha256='f'*64, report_sha256=digest)))
            with zipfile.ZipFile(str(report) + '.materials.zip', 'w'): pass
        seed(old_records)
        self.assertEqual(run()['status'], 'reuse')
        self.write('D5/Base.lean', 'def base := 2\n')
        changed = run()
        self.assertEqual(changed['changed'], ['D5.Base'])
        self.assertEqual(changed['recheck'], ['D5.Base', 'D5.Claim', 'D5.Consumer', 'Trureturing'])
        (self.repo / 'D5/Base.lean').rename(self.repo / 'D5/BaseRenamed.lean')
        renamed = run()
        self.assertEqual(renamed['removed'], ['D5.Base'])
        self.assertEqual(renamed['added'], ['D5.BaseRenamed'])
        self.assertEqual(renamed['recheck'], ['D5.BaseRenamed', 'D5.Claim', 'D5.Consumer', 'Trureturing'])
        (self.repo / 'D5/BaseRenamed.lean').unlink()
        deleted = run()
        self.assertEqual(deleted['removed'], ['D5.Base'])
        self.assertEqual(deleted['recheck'], ['D5.Claim', 'D5.Consumer', 'Trureturing'])
        old_records[1]['source_path'] = 'D5/Unregistered.lean'
        seed(old_records)
        with self.assertRaisesRegex(ValueError, 'Unregistered'):
            run()
        seed(old_records[2:])
        Path(str(report) + '.sha256').write_text('corrupt')
        self.assertEqual(run()['status'], 'fallback')

    def malformed_seed_fallback(self, damages):
        module_spec = importlib.util.spec_from_file_location('delta', self.repo / 'tools/lean-inspector/delta.py')
        delta = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(delta)
        current = self.selection().modules()
        table, output, cache = self.repo / 'modules.tsv', self.repo / 'plan.json', self.repo / 'cache'
        table.write_text(''.join(name + '\t' + path + '\n' for name, path in current.items()))
        records = [dict(module=name, source_path=path,
            source_sha256='sha256:' + hashlib.sha256((self.repo / path).read_bytes()).hexdigest(),
            imports=[], declarations=[dict(type_sha256='sha256:' + 'e'*64, statement_id='sha256:' + 'f'*64)])
            for name, path in current.items()]
        def seed(entry, damage=None):
            entry.mkdir(parents=True)
            root = dict(schema='stratalint-raw-lean-report-v2', modules=copy.deepcopy(records))
            if damage and damage[0] == 'root': root = damage[1]
            elif damage and damage[0] != 'provenance': root['modules'][0]['declarations'][0][damage[0]] = damage[1]
            report = entry / 'raw-lean-report.json'
            report.write_text(json.dumps(root))
            digest = hashlib.sha256(report.read_bytes()).hexdigest()
            Path(str(report) + '.sha256').write_text(digest + '  raw-lean-report.json\n')
            Path(str(report) + '.input.attestation').write_text(
                'schema=stratalint-lean-report-input-attestation-v1\nrepository_input_sha256=' + 'e'*64
                + '\nproducer_sha256=' + 'b'*64 + '\nreport_sha256=' + digest + '\n')
            provenance = dict(schema='stratalint-lean-report-provenance-v1', side='candidate', mode='produced',
                source_side='candidate', input_address='sha256:' + entry.name, producer_sha256='b'*64,
                repository_inspector_sha256='b'*64, lean_config_sha256='c'*64,
                lean_sources_sha256='f'*64, report_sha256=digest)
            if damage and damage[0] == 'provenance': provenance = damage[1]
            Path(str(report) + '.provenance.json').write_text(json.dumps(provenance))
            with zipfile.ZipFile(str(report) + '.materials.zip', 'w'): pass
            return report
        def run():
            result = subprocess.run([sys.executable, '-B', str(self.repo / 'tools/lean-inspector/delta.py'),
                'plan', str(self.repo), str(cache), 'a'*64, 'b'*64, 'b'*64, 'c'*64, str(table), str(output)],
                text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            return json.loads(output.read_text())
        for damage in damages:
            for older in (False, True):
                with self.subTest(damage=damage, older=older):
                    if cache.exists(): shutil.rmtree(cache)
                    invalid = cache / ('d'*64)
                    report = seed(invalid, damage)
                    os.utime(invalid, ns=(2000000000, 2000000000))
                    if older:
                        valid = cache / ('9'*64)
                        seed(valid)
                        os.utime(valid, ns=(1000000000, 1000000000))
                    result = run()
                    self.assertEqual(result['status'], 'reuse' if older else 'fallback')
                    if older:
                        self.assertEqual(result['baseline'], str(valid / 'raw-lean-report.json'))
                        self.assertEqual(result['recheck'], [])
                    # The public validation boundary must also reject decoded
                    # nonobjects without relying on the planner's early filter.
                    self.assertIsNone(delta.valid_baseline(invalid, 'a'*64, 'b'*64, 'b'*64, 'c'*64))
                    if damage[0] != 'provenance':
                        with self.assertRaisesRegex(ValueError, 'report schema|module record'):
                            delta.parse_json_modules(report)

    def test_malformed_provenance(self):
        self.malformed_seed_fallback([('provenance', None), ('provenance', [])])

    def test_malformed_reports(self):
        self.malformed_seed_fallback([('root', None), ('root', []),
            ('type_sha256', None), ('statement_id', [])])

    def test_delta_records(self):
        module_spec = importlib.util.spec_from_file_location('delta', self.repo / 'tools/lean-inspector/delta.py')
        delta = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(delta)
        selection = self.selection()
        current = {name: dict(path=path, source_sha256='sha256:' + hashlib.sha256((self.repo / path).read_bytes()).hexdigest())
            for name, path in selection.modules().items()}
        self.assertEqual(list(current), ['Trureturing', 'D5.Alone', 'D5.Base', 'D5.Claim', 'D5.Consumer'])
        # Merge protects subset, deletions and each source binding, preserving raw bytes.
        material = b'canonical statement fixture'
        material_address = 'sha256:' + hashlib.sha256(b'trureturing:statement:v1\0' + material).hexdigest()
        def record(name):
            return dict(module=name, source_path=current[name]['path'], source_sha256=current[name]['source_sha256'],
                imports=[], declarations=[dict(type_sha256=material_address, statement_id='sha256:' + 'e'*64)])
        def report(records):
            return delta.PREFIX + ', '.join(records) + delta.SUFFIX
        old = self.repo / 'old.json'
        stable = json.dumps(record('D5.Alone'), indent=2)
        old.write_text(report([stable] + [json.dumps(record(n)) for n in current if n != 'D5.Alone']))
        subset = self.repo / 'subset.json'
        subset.write_text(report([json.dumps(record('D5.Base'))]))
        for path in (old, subset):
            with zipfile.ZipFile(str(path) + '.materials.zip', 'w') as z:
                z.writestr('sha256/' + material_address[7:], material)
        plan = dict(baseline=str(old), recheck=['D5.Base'], removed=[], current=current)
        plan_file = self.repo / 'plan.json'
        output = self.repo / 'out.json'
        args = type('Args', (), dict(plan=str(plan_file), subset=str(subset), output=str(output)))()
        plan_file.write_text(json.dumps(plan))
        delta.merge(args)
        self.assertEqual(delta.raw_modules(output)['D5.Alone'][0], stable)
        for failure in ('subset', 'deletion', 'source', 'retained-source'):
            bad = copy.deepcopy(plan)
            if failure == 'subset': bad['recheck'] = []
            elif failure == 'deletion': bad['removed'] = ['D5.Alone']
            else: bad['current']['D5.Base' if failure == 'source' else 'D5.Alone']['source_sha256'] = 'sha256:' + '0' * 64
            plan_file.write_text(json.dumps(bad))
            with self.assertRaises(ValueError): delta.merge(args)
        plan_file.write_text(json.dumps(plan))
        before = output.read_bytes()
        with zipfile.ZipFile(str(subset) + '.materials.zip', 'w') as z:
            z.writestr('sha256/' + material_address[7:], b'wrong material with valid ZIP CRC')
        with self.assertRaisesRegex(ValueError, 'material address mismatch'):
            delta.merge(args)
        self.assertEqual(output.read_bytes(), before)


unittest.main(argv=[sys.argv[0], 'Contract.test_' + SCENARIO])
