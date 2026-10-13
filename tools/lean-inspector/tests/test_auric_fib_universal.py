#!/usr/bin/env python3
"""Real B1 clients through Lake report facets and the canonical artifact consumer.

The command guard bounds infrastructure. No duration is a correctness criterion.
Each fixture source and artifact belongs solely to this invocation.
"""
import hashlib
import copy
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector'))
import fib_analysis
import publication
import native
from test_auric_fib_analysis import assert_layer_limit

PREVIOUS_FORMAT = "stratalint-raw-lean-report-v3"


def previous_partial_artifact(artifact, directory):
    """Canonical prior-reading fixture; compiled requests/materials/origin stay real.

    This fixture is created during this test, not a historical occurrence.
    The old partial parser rejected every schedule missing the full catalog.
    """
    report = directory / "previous-raw-lean-report.json"
    with zipfile.ZipFile(artifact) as bundle:
        for suffix in native.ROW_SUFFIXES:
            Path(str(report) + suffix).write_bytes(bundle.read(publication.RAW + suffix))
    row = publication.validate_rows(report, Path(str(report) + ".materials.zip"))[0]
    origin = publication.validate_origin(report, [row])
    partition = row["fib_analysis"]
    partition["schema_version"] = 1
    for leaf in partition["applications"]:
        request = leaf["request"]
        if request is not None and request.get("arena", "native-single-window") == "native-single-window":
            selected = set(request.get("initial_readouts", [])) | set(request.get("layers", []))
            if len(request.get("layers", [])) > 64 or selected != {"atom", "seam", "guard", "reply"}:
                reading = dict.fromkeys(fib_analysis.FIELDS)
                reading["arena"] = dict(kind="invalid-input", cardinality=None, ordered_pair_denominator=None)
                reason = ("at most 64 finite successor layers are supported" if len(request.get("layers", [])) > 64
                    else "the complete atom,seam,guard,reply bundle must remain in the final layer")
                reading["disposition"] = dict(status="refuted", reason=reason, is_lean_proof=False,
                    proof_escape="unchanged; downstream analysis only",
                    physical_source_law="unknown; input validation is not source certification",
                    multiwindow_continuation="unknown; no multiwindow joint contract",
                    cost_and_research_value="not assessed; no aggregate score",
                    readings={key: dict(kind="unavailable", reason=reason)
                              for key in fib_analysis.FIELDS - {"disposition"}})
                leaf["reading"] = reading
    report.write_bytes(publication.materials.canonical_json(dict(
        schema=publication.materials.REPORT_SCHEMA, modules=[row])))
    publication.write_origin(report, row["module"],
        {key: origin[key] for key in ("producer_sources_sha256", "inspector_executable_sha256")},
        origin["input_projection"])
    # Statement materials were validated before the reading-only transform;
    # their bytes stay untouched. The current reader must reject this partition.
    publication.validate_origin(report, [row])
    temporary = artifact.with_suffix('.prior-fixture.tmp')
    publication.zip_files(temporary, [(publication.RAW + suffix, publication.member(report, suffix))
                                      for suffix in native.ROW_SUFFIXES])
    os.replace(temporary, artifact)
    return row

MODULE = 'Reg.Support.AuricFibUniversalFixture'
SIBLING = 'Reg.Support.AuricFibUniversalSibling'
DATA = 'Reg.Support.AuricFibUniversalData'
PREFIX = 'AuricFibUniversalProduction.'
STATE = ROOT / '.lake/build/lean-inspector'


class UniversalProductionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory(prefix='auric-fib-universal.')
        cls.directory = Path(cls.work.name)
        cls.sources = [ROOT / (name.replace('.', '/') + '.lean') for name in (MODULE, SIBLING, DATA)]
        cls.artifacts = [STATE / 'modules' / (name + '.zip') for name in (MODULE, SIBLING)]
        owned_outputs = [Path(str(path) + suffix) for path in cls.artifacts
                         for suffix in ('', '.pending', '.fib-previous')]
        if any(path.exists() for path in cls.sources + owned_outputs):
            raise RuntimeError('universal fixture is already owned; refusing takeover')
        cls.addClassCleanup(cls.cleanup)
        cls.environment = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
        cls.diagnostics = Path(os.environ.get('FIB_UNIVERSAL_DIAGNOSTICS', cls.directory))
        cls.diagnostics.mkdir(parents=True, exist_ok=True)
        cls.sequence = 0
        cls.source = '''import LeanInformationAuditInterface.Contract.AuricFib
namespace AuricFibUniversalData
private def acquired : Nat := 1
def mass : Nat := acquired
def denominator : Nat := 5
theorem source : type_of% D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=
  D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution
end AuricFibUniversalData
'''
        # Keep the dynamically compiled package within Reg's dependency boundary.
        # Reuse the source-owned B1 clients and compile the verification data in
        # the same fixture module, without importing a downstream test package.
        fixture_root = ROOT / 'tools/lean-inspector/LeanInformationAuditRegTests/AuricFib'
        native_fixture = (fixture_root / 'CompiledFixture.lean').read_text()
        native_fixture = native_fixture.replace(
            'LeanInformationAuditRegTests.AuricFib.CompiledFixture', 'AuricFibUniversalCompiled')
        generic_fixture = (fixture_root / 'UniversalFixture.lean').read_text().replace(
            'import LeanInformationAuditRegTests.AuricFib.CompiledFixture\n', '')
        generic_fixture = generic_fixture.replace(
            'LeanInformationAuditRegTests.AuricFib.CompiledFixture', 'AuricFibUniversalCompiled').replace(
            'LeanInformationAuditRegTests.AuricFib.UniversalFixture', 'AuricFibUniversalProduction')
        generic_fixture = generic_fixture.replace('owner := `AuricFibUniversalProduction',
                                                  'owner := `' + MODULE)
        imports = [line for text in (native_fixture, generic_fixture) for line in text.splitlines()
                   if line.startswith('import ')]
        bodies = ['\n'.join(line for line in text.splitlines() if not line.startswith('import '))
                  for text in (native_fixture, generic_fixture)]
        cls.application = ('import ' + DATA + '\n' + '\n'.join(dict.fromkeys(imports)) + '\n'
                           + '\n'.join(bodies)) + '''
namespace AuricFibUniversalProduction
open LeanInformationAudit.AuricFib.Contract
def changedLaw : Application.{0,0,0,0,0,0} AuricFibUniversalData.source where
  evidence := .native { reconstruction := .exact }
    AuricFibUniversalCompiled.bridge
    (.declared "actual private compiled dependency" {
      nullMass := AuricFibUniversalData.mass, lowMass := 1, highMass := 1,
      endsMass := 1, middleMass := 1, denominator := AuricFibUniversalData.denominator,
      positive := by decide, normalized := by decide }) [] [.seam, .guard, .reply, .atom]
end AuricFibUniversalProduction
'''
        cls.sources[0].write_text(cls.application)
        cls.sources[1].write_text('import LeanInformationAuditInterface.Contract.AuricFib\n'
            'namespace AuricFibUniversalSibling\n'
            'def unchanged : LeanInformationAudit.AuricFib.Contract.Application.{0,0,0,0,0,0} '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution where\n'
            '  evidence := .unsupported "no acquired contract for this adapter"\n'
            'end AuricFibUniversalSibling\n')
        cls.sources[2].write_text(cls.source)
        # Acquire real compiler inputs under the retired semantic identifier.
        reader = ROOT / 'tools/scripts/report/lean-report-selection.py'
        original, metadata = reader.read_bytes(), reader.stat()
        retired = original.replace(publication.selection.REPORT_FORMAT.encode(), PREVIOUS_FORMAT.encode())
        reader.write_bytes(retired)
        try:
            fresh = cls.build()
            cls.previous_row = previous_partial_artifact(cls.artifacts[0], cls.directory)
            cls.previous_artifact = cls.directory / 'previous-module.zip'
            shutil.copyfile(cls.artifacts[0], cls.previous_artifact)
            sibling_prior = cls.directory / 'previous-sibling'
            sibling_prior.mkdir()
            previous_partial_artifact(cls.artifacts[1], sibling_prior)
            # Same detached metadata/closure, retired partition: reissue every
            # leaf through the production producer, with no fabricated binding.
            current = copy.deepcopy(cls.previous_row)
            current['fib_analysis']['schema_version'] = 2
            for leaf in current['fib_analysis']['applications']:
                leaf['reading'] = None
            stats = fib_analysis.produce(current, cls.previous_artifact,
                ROOT / 'tools/scripts/auric-fib-analysis.sh')
            if stats['reused'] != 0:
                raise AssertionError('same-metadata prior-format leaves survived migration')
            generated = {row['application'].removeprefix(PREFIX): row
                         for row in current['fib_analysis']['applications']
                         if row['application'].startswith(PREFIX)}
            if generated != fresh:
                raise AssertionError('same-metadata migration differs from complete acquisition')
            cls.current_complete_row = current
            try:
                fib_analysis.consume(cls.directory / 'previous-raw-lean-report.json')
            except ValueError as error:
                if str(error) != 'fib.invalid_partition':
                    raise
            else:
                raise AssertionError('consumer accepted a retired reading partition')
            # The canonical former reading is really reusable at module level.
            prior_stamp = (publication.digest(cls.artifacts[0]), cls.artifacts[0].stat().st_mtime_ns)
            cls.command([MODULE + ':report'])
            if prior_stamp != (publication.digest(cls.artifacts[0]), cls.artifacts[0].stat().st_mtime_ns):
                raise AssertionError('previous-format no-op changed the canonical fixture')
            if cls.counts.get('extract', 0) != 0:
                raise AssertionError('previous-format fixture was not reusable')
        finally:
            reader.write_bytes(original)
            os.chmod(reader, metadata.st_mode)
            os.utime(reader, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
        sources = {p: publication.digest(p) for p in cls.sources}
        compiled = {p: (publication.digest(p), p.stat().st_mtime_ns)
                    for name in (MODULE, SIBLING, DATA)
                    for p in (ROOT / '.lake/build/reg/lib/lean').glob(name.replace('.', '/') + '.*')}
        if not compiled or not any(p.suffix == '.olean' for p in compiled):
            raise AssertionError('migration requires real Reg compiler artifacts')
        cls.first = cls.build(migration=True)
        if sources != {p: publication.digest(p) for p in cls.sources}:
            raise AssertionError('migration changed authored sources')
        if publication.validate_rows(cls.report, Path(str(cls.report) + '.materials.zip'))[0] != cls.current_complete_row:
            raise AssertionError('migrated complete module differs from current complete output')
        if compiled != {p: (publication.digest(p), p.stat().st_mtime_ns) for p in compiled}:
            raise AssertionError('semantic migration recompiled Reg inputs')
        if cls.counts.get('extract') != 2 or cls.counts.get('fib-reused', 0) != 0:
            raise AssertionError('semantic migration did not retire module and leaf reuse')
        if cls.first != fresh:
            raise AssertionError('migrated readings differ from current complete acquisition')
        print('UNIVERSAL_ANALYSIS_MIGRATION ' + json.dumps(dict(
            previous_format=PREVIOUS_FORMAT, current_format=publication.selection.REPORT_FORMAT,
            previous_schema=1, current_schema=2, unchanged_reg_compiler_artifacts=len(compiled),
            same_compiled_inputs=True, current_complete_equal=True, actual_work=cls.counts,
            previous_artifact_sha256=publication.digest(cls.previous_artifact),
            source_sha256={str(p.relative_to(ROOT)): sha for p, sha in sources.items()},
            partial_input_identity=next(x['input_identity'] for x in cls.previous_row['fib_analysis']['applications']
                                        if x['application'] == PREFIX + 'nativeAbsent'))), flush=True)

    @classmethod
    def cleanup(cls):
        for path in cls.sources:
            path.unlink(missing_ok=True)
        # Only invocation-owned fixture artifacts are removed; no shared report,
        # protected source-owned module, or other flight's artifact is touched.
        for name in (MODULE, SIBLING, DATA):
            for folder, suffixes in [('modules', ['.zip', '.zip.trace', '.zip.hash',
                                                  '.zip.pending', '.zip.fib-previous']),
                                     ('inputs', ['.json', '.json.sources.json']),
                                     ('judge-inputs', ['.json', '.json.trace', '.json.hash'])]:
                for suffix in suffixes:
                    (STATE / folder / (name + suffix)).unlink(missing_ok=True)
        cls.work.cleanup()

    @classmethod
    def command(cls, targets, *, full=False, expected=0):
        started = time.monotonic()
        cls.sequence += 1
        log = cls.diagnostics / f'command-{cls.sequence}.log'
        activity = cls.diagnostics / f'activity-{cls.sequence}.jsonl'
        env = dict(cls.environment, STRATALINT_INSPECTOR_ACTIVITY=str(activity),
                   STRATALINT_INSPECTOR_PROFILE='1')
        if full:
            env['LAKE_ARTIFACT_CACHE'] = 'false'
        command = ['bash', 'tools/scripts/worktree/lean-cache-run.sh', 'lake', '-d',
                   'tools/lean-inspector-reg', 'build', *targets]
        with (cls.diagnostics / 'commands.jsonl').open('a') as sink:
            sink.write(json.dumps(dict(command=command, stage='started', full=full, log=str(log))) + '\n')
        process = subprocess.Popen(command, cwd=ROOT, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=300)
        except subprocess.TimeoutExpired as error:
            # End only this invocation's process group; a timed-out compiler
            # must not continue writing after fixture cleanup.
            os.killpg(process.pid, signal.SIGTERM)
            try:
                stdout, stderr = process.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                stdout, stderr = process.communicate()
            log.write_text(stdout + stderr)
            with (cls.diagnostics / 'commands.jsonl').open('a') as sink:
                sink.write(json.dumps(dict(command=command, stage='infrastructure-unresolved',
                                           guard_seconds=300, log=str(log))) + '\n')
            raise RuntimeError(f'INFRASTRUCTURE_UNRESOLVED: 300-second guard: {log}') from error
        result = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
        log.write_text(result.stdout + result.stderr)
        with (cls.diagnostics / 'commands.jsonl').open('a') as sink:
            sink.write(json.dumps(dict(command=command, exit=result.returncode,
                                       log=str(log), full=full)) + '\n')
        if result.returncode != expected:
            raise AssertionError(f'expected exit {expected}; actual {result.returncode}; {log}\n'
                                 + result.stdout[-4000:] + result.stderr[-4000:])
        cls.counts = {}
        for line in activity.read_text().splitlines() if activity.exists() else []:
            row = json.loads(line)
            cls.counts[row['kind']] = cls.counts.get(row['kind'], 0) + row['count']
        print('UNIVERSAL_ANALYSIS_WORK ' + json.dumps(dict(sequence=cls.sequence,
            exit=result.returncode, elapsed_seconds=time.monotonic() - started,
            full=full, actual_work=cls.counts)), flush=True)
        return result

    @classmethod
    def build(cls, *, full=False, migration=False):
        sibling_before = ((hashlib.sha256(cls.artifacts[1].read_bytes()).hexdigest(),
                           cls.artifacts[1].stat().st_mtime_ns)
                          if cls.artifacts[1].exists() else None)
        if full:
            previous_reports = {}
            for artifact in cls.artifacts:
                with zipfile.ZipFile(artifact) as bundle:
                    previous_reports[artifact.name] = bundle.read('raw-lean-report.json')
            # These two fixture artifacts were created by this invocation.
            for artifact in cls.artifacts:
                for suffix in ('', '.trace', '.hash'):
                    Path(str(artifact) + suffix).unlink(missing_ok=True)
        # The facets compile their source/export closures and share Lake's
        # preparation in one invocation. Keep the existing per-command guard.
        cls.command([name + ':report' for name in (MODULE, SIBLING)], full=full)
        if full:
            if cls.counts.get('extract', 0) != len(cls.artifacts) or cls.counts.get('fib-reused', 0):
                raise AssertionError('complete report did not independently extract both fixture modules')
            for artifact in cls.artifacts:
                with zipfile.ZipFile(artifact) as bundle:
                    if previous_reports[artifact.name] != bundle.read('raw-lean-report.json'):
                        raise AssertionError('complete compiler report differs from incremental: ' + artifact.name)
            print('UNIVERSAL_ANALYSIS_COMPLETE ' + json.dumps(dict(
                modules=len(cls.artifacts), compiler_reports_byte_equal=True,
                actual_work=cls.counts)), flush=True)
        if not full and not migration and sibling_before is not None:
            sibling_after = (hashlib.sha256(cls.artifacts[1].read_bytes()).hexdigest(),
                             cls.artifacts[1].stat().st_mtime_ns)
            if sibling_before != sibling_after:
                raise AssertionError('unaffected sibling module bytes or writing time changed')
        for name, artifact in zip((MODULE, SIBLING), cls.artifacts):
            shutil.copyfile(artifact, cls.diagnostics / f'{cls.sequence}-{name}.zip')
        report = cls.directory / 'raw-lean-report.json'
        with zipfile.ZipFile(cls.artifacts[0]) as bundle:
            for suffix in ('', '.materials.zip', '.provenance.json'):
                Path(str(report) + suffix).write_bytes(bundle.read('raw-lean-report.json' + suffix))
        rows = publication.validate_rows(report, Path(str(report) + '.materials.zip'))
        cls.report = report
        consumed = fib_analysis.consume(report)
        (cls.diagnostics / f'consumed-{cls.sequence}.json').write_bytes(
            publication.materials.canonical_json(consumed))
        # Exercise the production aggregator on these real module artifacts.
        # Its private fixture input manifest selects only this test's modules;
        # it does not touch the repository's aggregate or full-project custody.
        aggregate_root = cls.directory / 'aggregate-root'
        aggregate_state = aggregate_root / '.lake/build/lean-inspector'
        aggregate_state.mkdir(parents=True, exist_ok=True)
        (aggregate_state / 'inputs.json').write_bytes(publication.materials.canonical_json(dict(
            modules=[MODULE, SIBLING], coordinates=publication.coordinates(ROOT))))
        aggregate = cls.directory / 'aggregate.zip'
        native.aggregate(aggregate_root, aggregate, *cls.artifacts)
        shutil.copyfile(aggregate, cls.diagnostics / f'{cls.sequence}-aggregate.zip')
        destination = cls.directory / 'aggregate-consumer'
        destination.mkdir(exist_ok=True)
        combined = fib_analysis.consume(publication.unpack(aggregate, destination))
        if len(combined['applications']) != len(consumed['applications']) + 1:
            raise AssertionError('aggregate membership or provenance lost a compiled application')
        if len(rows) != 1 or rows[0]['module'] != MODULE:
            raise AssertionError('wrong canonical module artifact')
        return {row['application'].removeprefix(PREFIX): row for row in consumed['applications']
                if row['application'].startswith(PREFIX)}

    def test_data_free_ingress(self):
        # Add a real author client for the existing bare proposition after the
        # original missing-contract check. No replacement theorem is introduced.
        before = self.build()
        type(self).application += """
namespace AuricFibUniversalProduction
open LeanInformationAudit.Analysis LeanInformationAudit.AuricFib.Contract
universe u
def dataFree : Application absentContract where
  evidence := .typed dataFreeClient
def terminalCounts : Application absentContract where
  evidence := .typed {
    source := dataFreeSource, plan := dataFreeClient.plan,
    acquisition := .finite (Domain.fiber dataFreeSource ()) terminalPresentation }
def dataFreeBad : Application absentContract where
  evidence := .typed {
    source := unobservedMismatch
    plan := { task := (), initial := [], additions := [] }
    acquisition := .unavailable "no finite presentation requested" }
def unobservedFamily : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{u}) where
  evidence := .typed {
    source := Source.unobserved _ `D5.S0.Diagonal.PigeonholeFiber
    plan := { task := (), initial := [], additions := [[], [()]] }
    acquisition := .unavailable "no finite presentation requested" }
end AuricFibUniversalProduction
"""
        self.sources[0].write_text(self.application)
        current = self.build()
        for name, target, telescope, levels in (
                ('dataFree', PREFIX + 'absentContract', 0, 0),
                ('unobservedFamily', 'D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber', 4, 1)):
            row = current[name]
            self.assertIsNotNone(row['request'], row)
            reading = row['reading']
            binding = reading['source_contract']['binding']
            self.assertEqual(binding['occurrence']['source_name'], target)
            self.assertEqual(binding['occurrence']['original_type']['identity'], row['target_type_identity'])
            self.assertEqual(binding['telescope_size'], telescope)
            self.assertEqual(binding['level_count'], levels)
            self.assertEqual(binding['coordinates'], [])
            self.assertEqual(binding['readouts'], [])
            self.assertIn('terminal model', binding['source_correspondence'])
            self.assertEqual(reading['disposition']['readings']['source_contract']['kind'], 'available')
            self.assertEqual(reading['disposition']['readings']['escape_rate']['kind'], 'unavailable')
            self.assertIsNone(reading['escape_rate'])
            self.assertIsNone(reading['pyramid_coordinates'])
            self.assertLessEqual(set(binding['accepted_axioms']), {'propext', 'Classical.choice', 'Quot.sound'})
            selected = fib_analysis.consume(self.report, [target])
            self.assertIn(row, selected['applications'])
        terminal = current['terminalCounts']
        self.assertIsNotNone(terminal['request'])
        self.assertEqual(terminal['request']['acquisition']['kind'], 'unavailable')
        self.assertIn('fib.unobserved_source_domain_unacquired', terminal['request']['acquisition']['reason'])
        self.assertIsNone(terminal['reading']['escape_rate'])
        self.assertIsNone(terminal['reading']['arena']['cardinality'])
        self.assertEqual(terminal['reading']['disposition']['readings']['source_contract']['kind'], 'available')
        self.assertEqual(current['dataFree']['request']['plan']['additions'], [[], [0], []])
        self.assertEqual(current['dataFree']['request']['binding']['occurrence']['original_type']['head'], 'True')
        self.assertIsNone(current['dataFreeBad']['request'])
        self.assertEqual(current['dataFreeBad']['unavailable_reason'], 'fib.unobserved_model_mismatch')
        self.assertEqual(before, {k: v for k, v in current.items()
                                if k not in {'dataFree', 'dataFreeBad', 'terminalCounts', 'unobservedFamily'}})
        self.assertEqual(current, self.build(full=True))
        # Replaying genuine compiler JSON through the public entry retains
        # arithmetic but cannot retain the producer's source evidence claim.
        replay = subprocess.run(['bash', 'tools/scripts/auric-fib-analysis.sh', '--batch'],
            cwd=ROOT, input=json.dumps([current[k]['request'] for k in ('dataFree', 'quotient')]),
            text=True, capture_output=True, check=False)
        self.assertEqual(replay.returncode, 0, replay.stderr + replay.stdout)
        for raw, key in zip(json.loads(replay.stdout), ('dataFree', 'quotient')):
            self.assertEqual(raw['disposition']['readings']['source_contract']['kind'], 'unavailable')
            self.assertIsNone(raw['source_contract']['binding'])
            self.assertEqual(raw['escape_rate'], current[key]['reading']['escape_rate'])

    def check_program_rebuilding(self, expected):
        # This test owns its temporary edit to the production compiler it tests.
        # Report artifacts and mathematical source are not replaced or patched.
        program = ROOT / 'tools/lean-inspector/LeanInformationAudit/Contract/FibApplications.lean'
        original, metadata = program.read_bytes(), program.stat()
        valid = original + b'\nnamespace LeanInformationAudit.FibApplications\n' \
            b'private def programBuildProbe : Nat := 1\nend LeanInformationAudit.FibApplications\n'
        invalid = valid.replace(b'programBuildProbe : Nat := 1', b'programBuildProbe : Nat := true')
        stamps = [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                  for p in self.artifacts]
        program.write_bytes(valid)
        try:
            self.assertEqual(expected, self.build())
            self.assertEqual(self.counts.get('extract', 0), 0)
            self.assertEqual(stamps, [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                                     for p in self.artifacts])
            program_log = (self.diagnostics / f'command-{self.sequence}.log').read_text()
            self.assertIn('Built LeanInformationAudit.Contract.FibApplications', program_log)
            program.write_bytes(invalid)
            failed = self.command([MODULE + ':report'], expected=1)
            self.assertIn('FibApplications.lean', failed.stdout + failed.stderr)
            self.assertIn('error:', (failed.stdout + failed.stderr).lower())
            self.assertEqual(stamps, [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                                     for p in self.artifacts])
        finally:
            if program.read_bytes() not in (valid, invalid):
                raise RuntimeError('program changed outside the fixture; refusing overwrite')
            program.write_bytes(original)
            os.chmod(program, metadata.st_mode)
            os.utime(program, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
            self.command(['leanInspector/reportInspector'])
        self.assertEqual(program.read_bytes(), original)

    def test_compiled_clients_boundaries_and_incremental(self):
        current = self.first
        for key in ('finite', 'constant', 'quotient', 'restricted', 'empty', 'singleton', 'delayed', 'decodedNat'):
            self.assertIsNotNone(current[key]['request'], (key, current[key]))
            self.assertEqual(current[key]['request']['acquisition']['kind'], 'finite',
                             (key, current[key]['request']['acquisition']))
        finite = current['finite']['reading']
        self.assertEqual(finite['arena']['cardinality'], 3)
        self.assertEqual(finite['escape_pairs'], [[0, 2], [2, 0]])
        self.assertEqual(finite['escape_rate'], {'numerator': 2, 'denominator': 6})
        self.assertEqual([row['count'] for row in finite['layered_spectrum']['layers']], [4, 0, 0])
        self.assertEqual([row['count'] for row in current['delayed']['reading']['layered_spectrum']['layers']],
                         [0, 0, 4, 0])
        self.assertEqual(current['constant']['reading']['unique_capture'][0]['count'], 0)
        decoded = current['decodedNat']['reading']['continuation_target']['outputs']
        self.assertTrue(all(row['value'] == {'kind': 'text', 'value': 'seven'} for row in decoded))
        self.assertTrue(all(row['decoded']['literal'] == {'kind': 'nat', 'value': 7}
                            for row in decoded))
        opaque = current['opaqueLayers']['reading']
        self.assertIsNotNone(opaque['source_contract']['binding'])
        self.assertIsNotNone(opaque['kernel']['structural'])
        self.assertIsNone(opaque['kernel']['structural']['additions'])
        self.assertFalse(opaque['kernel']['structural']['available'])
        self.assertIn('fib.plan_layers_unavailable',
                      opaque['disposition']['readings']['escape_rate']['reason'])
        definition = current['specializedDefinition']['reading']['source_contract']['binding']
        self.assertEqual(definition['level_count'], 1)
        self.assertEqual(definition['definition']['name'], PREFIX + 'definedStatement')
        self.assertEqual(definition['occurrence']['universe_arguments'], ['Lean.Level.zero'])
        joined = current['joinedDefinition']['reading']['source_contract']['binding']
        self.assertEqual(joined['level_count'], 2)
        self.assertEqual(joined['definition']['name'], PREFIX + 'definedStatement')
        self.assertEqual(joined['occurrence']['universe_arguments'], ['Lean.Level.zero'] * 2)
        self.assertEqual(current['quotient']['reading']['arena']['presentation']['scope'], 'quotient')
        self.assertEqual(current['restricted']['reading']['arena']['presentation']['scope'], 'restriction')
        for key, count in [('empty', 0), ('singleton', 1)]:
            reading = current[key]['reading']
            self.assertEqual(reading['arena']['cardinality'], count)
            self.assertEqual(reading['escape_pairs'], [])
            self.assertIsNone(reading['escape_rate'])
            self.assertEqual(reading['disposition']['readings']['escape_rate']['kind'], 'not-applicable')
        for key, levels, binders in [('dependentFamily', 1, 4), ('history', 2, 13)]:
            reading = current[key]['reading']
            binding = reading['source_contract']['binding']
            self.assertEqual((binding['level_count'], binding['telescope_size']), (levels, binders))
            self.assertIsNotNone(reading['kernel']['structural'])
            self.assertIsNone(reading['escape_rate'])
            self.assertEqual(reading['disposition']['readings']['escape_rate']['kind'], 'unavailable')
        self.assertEqual(current['infinite']['reading']['disposition']['readings']['escape_rate']['kind'],
                         'not-applicable')
        self.assertIsNotNone(current['undecoded']['reading']['source_contract'])
        self.assertIn('fib.acquisition_', current['undecoded']['request']['acquisition']['reason'])
        self.assertEqual(current['wrongOwner']['unavailable_reason'], 'unclassified_form:source.owner')
        self.assertEqual(current['nativeWrongTarget']['unavailable_reason'],
                         'unclassified_form:source.statement_reconstruction')
        native = current['nativeDeclared']['reading']
        self.assertEqual(native['arena']['cardinality'], 5)
        self.assertEqual(native['arena']['ordered_pair_denominator'], 20)
        self.assertEqual(native['atom_readout']['mode_order'], ['null', '2', '5', '25', '3'])
        self.assertEqual(native['layered_spectrum']['partition_count'], 20)
        self.assertEqual(current['nativeAbsent']['reading']['disposition']['readings']['association_coordinate']['kind'],
                         'unknown')
        self.assertEqual(current['nativeZeroCondition']['reading']['disposition']['readings']['conditional_reply_law']['kind'],
                         'not-applicable')
        limited = current['nativeLayerLimited']
        self.assertEqual(len(limited['request']['layers']), 65)
        self.assertEqual(limited['reading']['source_contract']['binding'], limited['request']['binding'])
        assert_layer_limit(self, limited['reading'], current['nativeAbsent']['reading'], same_source=False)
        self.assertEqual(current['nativeUnavailableLaw']['reading']['arena']['cardinality'], 5)
        self.assertEqual(current['nativeUnavailableLaw']['reading']['disposition']['readings']['association_coordinate']['kind'],
                         'unavailable')
        missing = fib_analysis.consume(self.report, [PREFIX + 'absentContract'])
        self.assertIn('no acquired FIB', missing['applications'][0]['reading']['disposition']['reason'])
        for row in current.values():
            self.assertFalse(row['reading']['disposition']['is_lean_proof'])
            if row['request'] is not None:
                self.assertLessEqual(set(row['request']['binding']['accepted_axioms']),
                                     {'propext', 'Classical.choice', 'Quot.sound'})
        snapshots = [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns) for p in self.artifacts]
        self.assertEqual(current, self.build())
        self.assertEqual(snapshots, [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                                    for p in self.artifacts])
        self.assertEqual(self.counts.get('extract', 0), 0)
        type(self).source = self.source.replace('acquired : Nat := 1', 'acquired : Nat := 2').replace(
            'denominator : Nat := 5', 'denominator : Nat := 6')
        self.sources[2].write_text(self.source)
        changed = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 1)
        self.assertGreaterEqual(self.counts.get('fib-reused', 0), len(current) - 1)
        self.assertNotEqual(current['changedLaw']['input_identity'], changed['changedLaw']['input_identity'])
        self.assertNotEqual(current['changedLaw']['reading']['association_coordinate'],
                            changed['changedLaw']['reading']['association_coordinate'])
        self.assertEqual({k: v for k, v in current.items() if k != 'changedLaw'},
                         {k: v for k, v in changed.items() if k != 'changedLaw'})
        self.assertEqual(snapshots[1], (hashlib.sha256(self.artifacts[1].read_bytes()).hexdigest(),
                                       self.artifacts[1].stat().st_mtime_ns))
        self.assertEqual(changed, self.build(full=True))
        # A source proof dependency changes the actual closure even when the
        # target's type, numerical law and source display strings remain equal.
        type(self).source = self.source.replace(
            'theorem source : type_of%',
            'private theorem sourceDependency : type_of% '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=\n'
            '  D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution\n'
            'theorem source : type_of%').replace(
            'theorem source : type_of% '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=\n'
            '  D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution\n',
            'theorem source : type_of% '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=\n'
            '  sourceDependency\n')
        self.sources[2].write_text(self.source)
        source_changed = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 1)
        self.assertNotEqual(changed['changedLaw']['input_identity'], source_changed['changedLaw']['input_identity'])
        self.assertEqual(changed['changedLaw']['reading'], source_changed['changedLaw']['reading'])
        self.assertEqual(source_changed, self.build(full=True))
        # A semantically equal reader still changes its actual compiled input.
        type(self).application = self.application.replace(
            'fun a => rawTransition (rawMachine 0).start a',
            'fun a => rawTransition (rawMachine 0).start (id a)')
        self.sources[0].write_text(self.application)
        reader_changed = self.build()
        affected = {'nativeDeclared', 'nativeAbsent', 'nativeEmpirical', 'nativeApex',
                    'nativeZeroCondition', 'nativeLayerLimited', 'nativeWrongTarget',
                    'nativeParameterized', 'nativeUnavailableLaw', 'changedLaw'}
        self.assertEqual({key for key in source_changed
                          if source_changed[key]['input_identity'] != reader_changed[key]['input_identity']},
                         affected)
        for key in source_changed:
            self.assertEqual(source_changed[key]['reading'], reader_changed[key]['reading'])
        self.assertEqual(reader_changed, self.build(full=True))
        # Real membership and qualification changes; no synthetic partition.
        type(self).application = self.application.replace('def finite := finiteAnalysis',
            'def finite := constantAnalysis').replace('def constant := constantAnalysis\n', '')
        type(self).application += '\nnamespace AuricFibUniversalProduction\n' \
            'def added := Reg.D5.S0.Diagonal.PigeonholeFiber.quotientAnalysis\n' \
            'end AuricFibUniversalProduction\n'
        self.sources[0].write_text(self.application)
        members = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 2)
        self.assertNotIn('constant', members)
        self.assertIn('added', members)
        self.assertEqual(members['finite']['reading']['arena']['cardinality'], 2)
        self.assertEqual(source_changed['history'], members['history'])
        self.assertEqual(members, self.build(full=True))
        type(self).application = self.application.replace('def finite := constantAnalysis\n', '') + '\nnamespace AuricFibUniversalProduction\n' \
            'def finite := wrongOwner\nend AuricFibUniversalProduction\n'
        self.sources[0].write_text(self.application)
        qualified = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 0)
        self.assertIsNone(qualified['finite']['request'])
        self.assertEqual(qualified['finite']['unavailable_reason'], 'unclassified_form:source.owner')
        self.assertEqual(members['history'], qualified['history'])
        self.assertEqual(qualified, self.build(full=True))
        self.check_program_rebuilding(qualified)
        (self.diagnostics / 'verified.json').write_text(json.dumps(dict(
            applications=len(members), finite_rate=finite['escape_rate'],
            native_domain=native['atom_readout']['mode_order'],
            full_incremental_equivalence=True, unchanged_module_bytes_and_mtime=True,
            program_rebuilt_without_reading_invalidation=True, program_failure_propagated=True,
            accepted_axioms=sorted(set().union(*(set(row['request']['binding']['accepted_axioms'])
                for row in current.values() if row['request'] is not None))),
            protected_scope='only invocation-owned fixture module artifacts'), indent=2) + '\n')


if __name__ == '__main__':
    unittest.main()
