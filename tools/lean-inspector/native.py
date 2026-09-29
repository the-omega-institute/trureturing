#!/usr/bin/env python3
"""Production actions for Lake's Inspector facets; Lake owns module invalidation."""
from __future__ import annotations

import json
from contextlib import contextmanager
from functools import lru_cache
import hashlib
import os
from pathlib import Path
import stat
import struct
import subprocess
import sys
import tempfile
import time
import zipfile
import zlib

# Match zipfile's optional LZMA support; importing the producer must also work
# on Python installations without that decoder.
try:
    from lzma import LZMAError
except ImportError:
    LZMA_ERRORS = ()
else:
    LZMA_ERRORS = (LZMAError,)

ROW_ERRORS = (OSError, UnicodeError, ValueError, KeyError, TypeError,
              zipfile.BadZipFile, zlib.error, NotImplementedError) + LZMA_ERRORS

import materials
import publication as public

selection = public.selection
ROW_SUFFIXES = ('', '.materials.zip', '.provenance.json')
# Each native invocation imports the batch's environment and joins its whole
# registration universe; larger batches amortize that fixed cost. Each joined
# occurrence has its own heartbeat budget, so batch size does not bound it.
NATIVE_BATCH_MODULES = 100
UTILITY_FIELDS = {'modulePath', 'claimGid', 'claimModule', 'claimSelector', 'claimSourcePath',
                  'claimSourceSha256', 'resultGid', 'resultModule', 'resultSelector'}


def activity(kind, count):
    """Invocation-local work counts; these never participate in reuse decisions."""
    path = os.environ.get('STRATALINT_INSPECTOR_ACTIVITY')
    if path:
        with Path(path).open('a', encoding='utf-8') as target:
            target.write(json.dumps({'kind': kind, 'count': count}) + '\n')


def diagnostic_failure(label, error):
    try:
        print(f'LEAN_INSPECTOR_DIAGNOSTIC_UNAVAILABLE {label}: {error}', file=sys.stderr)
    except (OSError, UnicodeError):
        pass


@contextmanager
def phase(name, **context):
    """Flush invocation phase boundaries independently of buffered process IO."""
    path = os.environ.get('STRATALINT_INSPECTOR_PHASES')

    def emit(boundary, **fields):
        if path:
            try:
                with Path(path).open('a', encoding='utf-8') as target:
                    target.write(json.dumps(dict(phase=name, boundary=boundary,
                        monotonic_ms=time.monotonic_ns() // 1_000_000, **context, **fields)) + '\n')
            except (OSError, ValueError) as error:
                diagnostic_failure('native phases', error)

    emit('start')
    success = False
    try:
        yield
        success = True
    finally:
        emit('finish', success=success)


def retain_request(root, executable, arguments, utilities, origin=None):
    """Optional request evidence, never an input to report/cache acceptance.

    Keep the actual argument/utility order. Inspector.main derives its imports
    from these inputs; its source digest identifies that derivation, without
    maintaining an independent Python approximation of the import list.
    """
    phase_path = os.environ.get('STRATALINT_INSPECTOR_PHASES')
    if not phase_path:
        return None
    temporary = None
    try:
        payload = dict(cwd=str(root), executable=str(executable), arguments=arguments,
            utilities=utilities, origin=origin,
            inspector_source_sha256=public.digest(Path(root) / 'tools/lean-inspector/Inspector.lean'),
            inspector_executable_sha256=(origin['inspector_executable_sha256'] if origin
                else public.digest(executable)),
            lean_toolchain=(Path(root) / 'lean-toolchain').read_text(encoding='utf-8'))
        # Unique names preserve multiple native calls in one diagnostic directory.
        # Only the phase's request_capture identifies this call; old files alone
        # are not evidence that a later invocation captured or ran a request.
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8',
                prefix='native-request-', suffix='.json.tmp',
                dir=Path(phase_path).parent, delete=False) as target:
            temporary = Path(target.name)
            json.dump(payload, target)
            target.write('\n')
        capture = temporary.with_suffix('')
        os.replace(temporary, capture)
        return str(capture)
    except (OSError, UnicodeError, ValueError) as error:
        diagnostic_failure('native request capture', error)
        return None
    finally:
        if temporary is not None:
            try:
                temporary.unlink(missing_ok=True)
            except OSError as error:
                diagnostic_failure('native request temporary cleanup', error)


def state(root):
    return Path(root) / '.lake/build/lean-inspector'


def write_if_changed(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() == data:
        return
    # Never mutate a possible restored hard link in place.
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_bytes(data)
    os.replace(temporary, path)


@phase('native-inputs')
def prepare(root):
    root = Path(root).resolve()
    with phase('native-input-selection'):
        inputs = selection.Selection(root)
        inputs.validate('lean-report')
        modules = inputs.modules()
    producer = os.environ.get('STRATALINT_LEAN_PRODUCER_DLL')
    if producer:
        if not Path(producer).is_absolute() or not Path(producer).is_file():
            raise ValueError('candidate Lean producer must be an existing absolute path')
        command = ['dotnet', producer]
    else:
        command = ['dotnet', 'run', '--project', str(root / 'tools/StrataLint.Lean/StrataLint.Lean.csproj'),
            '--configuration', 'Release', '--no-build', '--no-restore', '--no-launch-profile', '--']
    with phase('native-utility-input'):
        result = subprocess.run([*command, 'lean-utility-input'],
            cwd=root, stdout=subprocess.PIPE, check=True)
    with phase('native-input-files'):
        utilities = public.read_json(result.stdout)
        if not isinstance(utilities, list):
            raise ValueError('utility input must be an array')
        by_path = {}
        for utility in utilities:
            materials.require_keys(utility, UTILITY_FIELDS, 'authoritative utility input')
            if any(not isinstance(value, str) or not value for value in utility.values()):
                raise ValueError('incomplete utility input')
            path = utility['modulePath']
            if path in by_path:
                raise ValueError('duplicate utility obligation')
            claim = inputs.safe_file(utility['claimSourcePath'])
            if utility['claimSourceSha256'] != 'sha256:' + public.digest(claim):
                raise ValueError('stale authoritative claim source')
            by_path[path] = utility
        for name, path in sorted(modules.items()):
            utility = [by_path[path]] if path in by_path else []
            write_if_changed(state(root) / 'inputs' / (name + '.json'), materials.canonical_json({
                'utilities': utility, 'claims': sorted({u['claimModule'] for u in utility}), 'source_path': path}))
        write_if_changed(state(root) / 'compatibility', (inputs.compatibility() + '\n').encode('ascii'))
    # Membership and full config identity affect aggregation only. Each module
    # traces compatibility, source, utility inputs and Lake's compiler dependencies.
    with phase('native-input-coordinates'):
        write_if_changed(state(root) / 'inputs.json', materials.canonical_json({
            'modules': sorted(modules),
            'configs': inputs.expand('config_inputs'), 'coordinates': public.coordinates(root)}))


@lru_cache(maxsize=None)
def source_inventory(root):
    # Expanded once per native invocation, never mixed into the aggregate
    # trace: adding an unused producer helper is still a compatible change.
    inputs = selection.Selection(root)
    return set(inputs.dependency_sources())


def validate_dependency_paths(root, utility_path):
    allowed = source_inventory(str(root))
    paths = public.read_json(Path(str(utility_path) + '.sources.json').read_bytes())
    materials.require_sorted_strings(sorted(set(paths)), 'native dependency sources')
    if set(paths) - allowed:
        raise ValueError('unregistered native dependency sources: ' + ', '.join(sorted(set(paths) - allowed)))


def row_binding(rows, root, module_name, utility_path, *, template_inputs=None):
    if len(rows) != 1 or rows[0]['module'] != module_name:
        raise ValueError('native module binding mismatch')
    row = rows[0]
    public.validate_template_sources(rows, root, inputs=template_inputs)
    record = public.read_json(Path(utility_path).read_bytes())
    path = record['source_path']
    if row['source_path'] != path:
        raise ValueError('native module source path mismatch')
    obligations = record['utilities']
    if not obligations:
        if 'utility_refutation' in row:
            raise ValueError('unexpected utility evidence')
    else:
        utility = obligations[0]
        evidence = row.get('utility_refutation', {})
        for raw, field in [('claimGid', 'claim_gid'), ('claimSourcePath', 'claim_source_path'),
                           ('claimSourceSha256', 'claim_source_sha256'), ('resultGid', 'result_gid')]:
            if evidence.get(field) != utility[raw]:
                raise ValueError('native utility binding mismatch')


def module(root, name, source, utility_path, executable, output):
    root, source, output = Path(root), Path(source), Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.module.', dir=output.parent) as directory:
        directory = Path(directory)
        record = public.read_json(Path(utility_path).read_bytes())
        validate_dependency_paths(root, utility_path)
        utility = directory / 'utility.json'
        utility.write_bytes(materials.canonical_json(record['utilities']))
        spool = directory / 'spool'
        spool.mkdir()
        report = directory / public.RAW
        arguments = ['--output', str(directory / 'spool.json'), '--material-spool', str(spool),
            '--utility-input', str(utility), name, record['source_path'], 'sha256:' + public.digest(source)]
        capture = retain_request(root, executable, arguments, record['utilities'])
        with phase('native-inspect', request_capture=capture):
            subprocess.run([str(executable), *arguments], check=True, cwd=root)
        materials.compact(directory / 'spool.json', spool, report, root / 'lean-report-inputs.json')
        # Lake returns only canonically validated public facets. Generation is
        # private; the completed artifact gets its full validation at acceptance.
        rows = public.read_json(report.read_bytes())['modules']
        row_binding(rows, root, name, utility_path)
        artifact = directory / 'module.zip'
        public.write_origin(report, name, public.production_origin(root, executable))
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in ROW_SUFFIXES])
        os.replace(artifact, output)
        activity('extract', 1)
        print(f'LEAN_INSPECTOR_EXTRACT module={name} declarations={len(rows[0]["declarations"])}')


def produce_batch_chunk(requests):
    root = Path(requests[0][0])
    template_inputs = selection.Selection(root)
    executable = requests[0][4]
    origin = public.production_origin(root, executable)
    if any(Path(row[0]) != root or row[4] != executable for row in requests):
        raise ValueError('mixed native batch owners')
    with tempfile.TemporaryDirectory(prefix='.inspection.', dir=state(root)) as directory:
        directory = Path(directory)
        spool = directory / 'spool'
        spool.mkdir()
        utilities = []
        triples = []
        bindings = {}
        for _, name, source, utility_path, _, output in requests:
            if name in bindings:
                raise ValueError('duplicate native batch module')
            record = public.read_json(Path(utility_path).read_bytes())
            utilities.extend(record['utilities'])
            triples.extend([name, record['source_path'], 'sha256:' + public.digest(source)])
            validate_dependency_paths(root, utility_path)
            bindings[name] = (utility_path, Path(output))
        utility_file = directory / 'utility.json'
        utility_file.write_bytes(materials.canonical_json(utilities))
        arguments = ['--output', str(directory / 'spool.json'), '--material-spool', str(spool),
                     '--utility-input', str(utility_file), *triples]
        argument_file = directory / 'arguments.json'
        argument_file.write_text(json.dumps(arguments))
        capture = retain_request(root, executable, arguments, utilities, origin)
        with phase('native-inspect', request_capture=capture):
            subprocess.run([executable, '--request-file', str(argument_file)], cwd=root, check=True)
        raw = public.read_json((directory / 'spool.json').read_bytes())
        if [row['module'] for row in raw['modules']] != sorted(bindings):
            raise ValueError('incomplete native inspection batch')
        for row in raw['modules']:
            name = row['module']
            utility_path, output = bindings[name]
            row_dir = directory / name
            row_dir.mkdir()
            row_spool = row_dir / 'spool'
            row_spool.mkdir()
            for decl in row['declarations']:
                source = materials.regular_spool_file(spool, decl['material_file'])
                os.replace(source, row_spool / source.name)
            spool_report = row_dir / 'spool.json'
            spool_report.write_bytes(materials.canonical_json({'schema': materials.SPOOL_SCHEMA, 'modules': [row]}))
            report = row_dir / public.RAW
            materials.compact(spool_report, row_spool, report, root / 'lean-report-inputs.json')
            rows = public.read_json(report.read_bytes())['modules']
            row_binding(rows, root, name, utility_path, template_inputs=template_inputs)
            output.parent.mkdir(parents=True, exist_ok=True)
            artifact = row_dir / 'module.zip'
            public.write_origin(report, name, origin)
            public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in ROW_SUFFIXES])
            os.replace(artifact, output)
        if list(spool.iterdir()):
            raise ValueError('unreferenced batch materials')
        activity('extract', len(requests))
        print(f'LEAN_INSPECTOR_EXTRACT modules={len(requests)} declarations={sum(len(row["declarations"]) for row in raw["modules"])}')


def produce_batch(requests):
    requests = sorted(requests, key=lambda row: row[1])
    if not requests:
        return
    root, executable = Path(requests[0][0]), requests[0][4]
    if any(Path(row[0]) != root or row[4] != executable for row in requests):
        raise ValueError('mixed native batch owners')
    if any(left[1] == right[1] for left, right in zip(requests, requests[1:])):
        raise ValueError('duplicate native batch module')
    # Chunks bound per-process memory; Lake still validates every
    # completed module facet and the full aggregate after these bounded calls.
    for start in range(0, len(requests), NATIVE_BATCH_MODULES):
        produce_batch_chunk(requests[start:start + NATIVE_BATCH_MODULES])


@phase('native-batch')
def batch(request_file, result_file):
    requests = public.read_json(Path(request_file).read_bytes())
    produce = [args for kind, args in requests if kind == 'produce']
    if produce:
        with phase('native-produce'):
            produce_batch(produce)
    statuses = []
    verified_materials = {}
    source_scopes = {}

    def template_inputs(root):
        root = Path(root).resolve()
        if root not in source_scopes:
            source_scopes[root] = selection.Selection(root)
        return source_scopes[root]

    # The canonical Lake batch asks for each module's validation followed by
    # aggregation of exactly those modules. The builder already performs that
    # same complete validation, so let its row results serve both demands.
    # Other request shapes retain the ordinary independent boundaries.
    if requests and requests[-1][0] == 'aggregate':
        root, output, *artifacts = requests[-1][1]
        config = public.read_json((state(root) / 'inputs.json').read_bytes())
        expected = [['validate', [root, 'module', root, name,
            str(state(root) / 'inputs' / (name + '.json')), artifact]]
            for name, artifact in zip(config['modules'], artifacts)]
        # Lake's FilePath retains /./ while pathlib renders the same lexical
        # path without it. Compare paths without resolving symlinks or '..'.
        same_requests = len(requests) == len(expected) + 1 and all(
            kind == wanted_kind and len(args) == len(wanted_args) and
            args[:4] == wanted_args[:4] and Path(args[4]) == Path(wanted_args[4]) and
            args[5:] == wanted_args[5:]
            for (kind, args), (wanted_kind, wanted_args) in zip(requests, expected))
        if expected and len(artifacts) == len(config['modules']) and same_requests:
            aggregate(root, output, artifacts, verified_materials=verified_materials,
                      template_inputs=template_inputs(root), row_statuses=statuses)
            statuses.append(int(any(statuses)))
            Path(result_file).write_text(json.dumps(statuses))
            return

    for kind, args in requests:
        if kind == 'produce':
            statuses.append(0)
        elif kind == 'validate':
            try:
                validate(*args[1:], verified_materials=verified_materials,
                         template_inputs=template_inputs(args[0]))
                statuses.append(0)
            except ROW_ERRORS as error:
                print(f'LEAN_INSPECTOR_REJECT {error}', file=sys.stderr)
                statuses.append(1)
        elif kind == 'aggregate':
            if any(statuses):
                statuses.append(1)
            else:
                root, output, *artifacts = args
                aggregate(root, output, artifacts, verified_materials=verified_materials,
                          template_inputs=template_inputs(root))
                statuses.append(0)
        else:
            raise ValueError('unknown native batch operation')
    Path(result_file).write_text(json.dumps(statuses))


def aggregate(root, output, artifacts, verified_materials=None, *, template_inputs=None, row_statuses=None):
    root, output = Path(root), Path(output)
    if template_inputs is None:
        template_inputs = selection.Selection(root)
    if verified_materials is None:
        verified_materials = {}
    config = public.read_json((state(root) / 'inputs.json').read_bytes())
    if len(artifacts) != len(config['modules']):
        raise ValueError('native aggregate membership mismatch')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.aggregate.', dir=output.parent) as directory, \
            tempfile.TemporaryFile(dir=output.parent) as material_spool:
        directory = Path(directory)
        material_offsets = {}
        rows = []
        origins = {}
        for name, artifact in zip(config['modules'], artifacts):
            with tempfile.TemporaryDirectory(prefix='row.', dir=directory) as row_dir:
                try:
                    utility = state(root) / 'inputs' / (name + '.json')
                    report = public.unpack(artifact, row_dir, ROW_SUFFIXES)
                    known = accepted(root, 'module', name, artifact, utility)
                    if known:
                        current = public.read_json(report.read_bytes())['modules']
                        origin = public.read_json(public.member(report, '.provenance.json').read_bytes())
                    else:
                        current, origin = validate_module(report, root, name, utility,
                            verified_materials=verified_materials, template_inputs=template_inputs)
                    if origin['compatibility_sha256'] != config['coordinates']['producer']:
                        raise ValueError('native aggregate compatibility mismatch')
                    if not known:
                        record_acceptance(root, 'module', name, artifact, utility)
                except ROW_ERRORS as error:
                    if row_statuses is None:
                        raise
                    print(f'LEAN_INSPECTOR_REJECT {error}', file=sys.stderr)
                    row_statuses.append(1)
                    continue
                if row_statuses is not None:
                    row_statuses.append(0)
                origins[name] = origin
                rows.extend(current)
                # Accepted materials match their content addresses; move their
                # deflated bytes without decompressing or compressing again.
                with zipfile.ZipFile(public.member(report, '.materials.zip')) as archive:
                    for entry in archive.infolist():
                        shape = (entry.CRC, entry.file_size)
                        if entry.filename in material_offsets:
                            if material_offsets[entry.filename][2:] != shape:
                                raise ValueError('statement material address collision')
                            continue
                        data = compressed_member(archive, entry)
                        material_spool.seek(0, os.SEEK_END)
                        material_offsets[entry.filename] = (material_spool.tell(), len(data), *shape)
                        material_spool.write(data)
        if row_statuses is not None and any(row_statuses):
            return
        report = directory / public.RAW
        report.write_bytes(materials.canonical_json({'modules': rows, 'schema': materials.REPORT_SCHEMA}))
        with zipfile.ZipFile(public.member(report, '.materials.zip'), 'w', compression=zipfile.ZIP_DEFLATED,
                             compresslevel=6, allowZip64=True) as archive:
            for name, (offset, size, crc, file_size) in sorted(material_offsets.items()):
                info = zipfile.ZipInfo(name, materials.ARCHIVE_TIMESTAMP)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                info.CRC, info.file_size = crc, file_size
                material_spool.seek(offset)
                data = material_spool.read(size)
                if len(data) != size:
                    raise ValueError('truncated private material spool')
                append_compressed(archive, info, data)
        public.write_sidecars(report, config['coordinates'], origins)
        # The bundle concatenates exactly the rows accepted above, in registered
        # order; checking it again would replay those judgements.
        artifact = directory / 'report.zip'
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in public.SUFFIXES])
        os.replace(artifact, output)
        record_acceptance(root, 'report', 'report', output, state(root) / 'inputs.json')
        activity('aggregate', 1)
        print(f'LEAN_INSPECTOR_AGGREGATE modules={len(rows)} declarations={sum(len(row["declarations"]) for row in rows)}')


def compressed_member(archive, info):
    """The stored deflate stream of one member, exactly as written."""
    if info.compress_type != zipfile.ZIP_DEFLATED or info.flag_bits & 1:
        raise ValueError('statement material is not a plain deflated member')
    archive.fp.seek(info.header_offset)
    header = archive.fp.read(30)
    if len(header) != 30 or header[:4] != b'PK\x03\x04':
        raise ValueError('invalid statement material header')
    name_length, extra_length = struct.unpack('<HH', header[26:30])
    archive.fp.seek(info.header_offset + 30 + name_length + extra_length)
    data = archive.fp.read(info.compress_size)
    if len(data) != info.compress_size:
        raise ValueError('truncated statement material')
    return data


def append_compressed(archive, info, data):
    """Lay out a deflated member exactly as ZipFile.open(info, 'w') does."""
    info.compress_size = len(data)
    info.flag_bits = 0
    archive.fp.seek(archive.start_dir)
    info.header_offset = archive.fp.tell()
    archive._writecheck(info)
    archive._didModify = True
    archive.fp.write(info.FileHeader(False))
    archive.fp.write(data)
    archive.start_dir = archive.fp.tell()
    archive.filelist.append(info)
    archive.NameToInfo[info.filename] = info


def acceptance_key(root, kind, name, *inputs):
    """Content address of one successful validation.

    Validation is a pure function of these bytes and the semantic version
    (compatibility); an identical key is the same judgement, never re-run.
    """
    compatibility = (state(root) / 'compatibility').read_text(encoding='ascii').strip()
    fields = [kind, name, compatibility, *(public.digest(path) for path in inputs)]
    return hashlib.sha256('\0'.join(fields).encode('utf-8')).hexdigest()


def acceptance_path(root, kind, name):
    # Host-local like .lake/lean-input-memo: seeds carry .lake/build, and a
    # transported record must never excuse transported bytes from validation.
    return Path(root) / '.lake/lean-inspector-accepted' / kind / name


def accepted(root, kind, name, *inputs):
    path = acceptance_path(root, kind, name)
    try:
        return path.read_text(encoding='ascii') == acceptance_key(root, kind, name, *inputs)
    except (OSError, UnicodeError):
        return False


def record_acceptance(root, kind, name, *inputs):
    write_if_changed(acceptance_path(root, kind, name),
                     acceptance_key(root, kind, name, *inputs).encode('ascii'))


def validate_module(report, root, name, utility, *, verified_materials=None, template_inputs=None):
    rows = public.validate_rows(report, public.member(report, '.materials.zip'), verified_materials,
                                manifest=Path(root) / 'lean-report-inputs.json')
    row_binding(rows, root, name, utility, template_inputs=template_inputs)
    # prepare validated the manifest before any facet could accept an artifact.
    compatibility = (state(root) / 'compatibility').read_text(encoding='ascii').strip()
    origin = public.validate_origin(report, rows, compatibility)
    return rows, origin


def validate_report(report, root, verified_materials, template_inputs):
    config = public.read_json((state(root) / 'inputs.json').read_bytes())
    rows = public.validate_bundle(report, config['coordinates'], root, verified_materials)
    if [row['module'] for row in rows] != config['modules']:
        raise ValueError('native aggregate membership mismatch')
    for row in rows:
        row_binding([row], root, row['module'], state(root) / 'inputs' / (row['module'] + '.json'),
                    template_inputs=template_inputs)


def validate(kind, root, *args, verified_materials=None, template_inputs=None):
    if kind == 'module':
        name, utility, artifact = args
        inputs = (artifact, utility)
    elif kind == 'report':
        name, inputs = 'report', (args[0], state(root) / 'inputs.json')
    else:
        raise ValueError('unknown native artifact kind')
    if accepted(root, kind, name, *inputs):
        return
    if template_inputs is None:
        template_inputs = selection.Selection(root)
    with tempfile.TemporaryDirectory(prefix='.validate.', dir=state(root)) as directory:
        if kind == 'module':
            report = public.unpack(artifact, directory, ROW_SUFFIXES)
            validate_module(report, root, name, utility, verified_materials=verified_materials,
                            template_inputs=template_inputs)
        else:
            validate_report(public.unpack(args[0], directory), root, verified_materials, template_inputs)
    record_acceptance(root, kind, name, *inputs)


def publish(root, destination):
    inputs = public.coordinates(root)
    with tempfile.TemporaryDirectory(prefix='.publish.', dir=state(root)) as directory:
        report = public.unpack(state(root) / 'report.zip', directory)
        activity_file = os.environ.get('STRATALINT_INSPECTOR_ACTIVITY')
        mode = None
        if activity_file:
            records = [public.read_json(line) for line in Path(activity_file).read_text().splitlines()]
            mode = 'produced' if records else 'cached'
            print(f'LEAN_INSPECTOR_WORK extracted_modules={sum(row["count"] for row in records if row["kind"] == "extract")} aggregates={sum(row["count"] for row in records if row["kind"] == "aggregate")}')
        # Lake's report facet recorded acceptance of these exact bytes; a
        # changed or unrecorded bundle takes the complete check.
        known = accepted(root, 'report', 'report', state(root) / 'report.zip', state(root) / 'inputs.json')
        public.publish(report, Path(destination), inputs, root, mode=mode, validate=not known)
    print(f'RAW_LEAN_REPORT path={destination} sha256={public.digest(destination)}')


def main():
    actions = {'prepare': prepare, 'module': module, 'aggregate': lambda root, output, *paths: aggregate(root, output, paths),
               'validate': validate, 'publish': publish, 'batch': batch}
    if len(sys.argv) < 2 or sys.argv[1] not in actions:
        raise ValueError('expected prepare, module, aggregate, validate, or publish')
    actions[sys.argv[1]](*sys.argv[2:])


if __name__ == '__main__':
    try:
        main()
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        print(f'lean-inspector-native: {error}', file=sys.stderr)
        raise SystemExit(1)
