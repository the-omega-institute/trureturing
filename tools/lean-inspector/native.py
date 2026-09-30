#!/usr/bin/env python3
"""Production actions for Lake's Inspector facets; Lake owns module invalidation."""
from __future__ import annotations

import json
from contextlib import contextmanager
from functools import lru_cache
import os
from pathlib import Path
import stat
import struct
import subprocess
import sys
import tempfile
import time
import zipfile

import materials
import publication as public

selection = public.selection
ROW_SUFFIXES = ('', '.materials.zip', '.provenance.json')
# Each native invocation imports the batch's environment and joins its whole
# registration universe. Bound per-invocation memory when reports are stale.
NATIVE_BATCH_MODULES = 8
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
        public.write_origin(report, name, public.production_origin(root, executable))
        # Like an olean, an artifact is validated once, when it is produced;
        # Lake's trace alone decides later reuse.
        rows, _ = validate_module(report, root, name, utility_path)
        artifact = directory / 'module.zip'
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in ROW_SUFFIXES])
        os.replace(artifact, output)
        activity('extract', 1)
        print(f'LEAN_INSPECTOR_EXTRACT module={name} declarations={len(rows[0]["declarations"])}')


def produce_batch_chunk(requests):
    root = Path(requests[0][0])
    template_inputs = selection.Selection(root)
    executable = requests[0][4]
    origin = public.production_origin(root, executable)
    verified_materials = {}
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
            public.write_origin(report, name, origin)
            validate_module(report, root, name, utility_path, verified_materials=verified_materials,
                            template_inputs=template_inputs)
            output.parent.mkdir(parents=True, exist_ok=True)
            artifact = row_dir / 'module.zip'
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
    # Chunks bound per-process memory; each chunk validates its modules
    # before writing their artifacts.
    for start in range(0, len(requests), NATIVE_BATCH_MODULES):
        produce_batch_chunk(requests[start:start + NATIVE_BATCH_MODULES])


@phase('native-batch')
def batch(request_file):
    requests = public.read_json(Path(request_file).read_bytes())
    produce = [args for kind, args in requests if kind == 'produce']
    if produce:
        with phase('native-produce'):
            produce_batch(produce)
    for kind, args in requests:
        if kind == 'aggregate':
            aggregate(*args)
        elif kind != 'produce':
            raise ValueError('unknown native batch operation')


def aggregate(root, output, *artifacts):
    """Concatenate module artifacts that were validated when produced."""
    root, output = Path(root), Path(output)
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
                report = public.unpack(artifact, row_dir, ROW_SUFFIXES)
                current = public.read_json(report.read_bytes())['modules']
                origin = public.read_json(public.member(report, '.provenance.json').read_bytes())
                if [row['module'] for row in current] != [name]:
                    raise ValueError('native aggregate membership mismatch')
                if origin['compatibility_sha256'] != config['coordinates']['producer']:
                    raise ValueError('native aggregate compatibility mismatch')
                origins[name] = origin
                rows.extend(current)
                # Produced materials matched their content addresses; move their
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
        artifact = directory / 'report.zip'
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in public.SUFFIXES])
        os.replace(artifact, output)
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


def validate_module(report, root, name, utility, *, verified_materials=None, template_inputs=None):
    rows = public.validate_rows(report, public.member(report, '.materials.zip'), verified_materials,
                                manifest=Path(root) / 'lean-report-inputs.json')
    row_binding(rows, root, name, utility, template_inputs=template_inputs)
    # prepare validated the manifest before any facet could accept an artifact.
    compatibility = (state(root) / 'compatibility').read_text(encoding='ascii').strip()
    origin = public.validate_origin(report, rows, compatibility)
    return rows, origin


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
        # Lake traced this aggregate of production-validated rows.
        public.publish(report, Path(destination), inputs, root, mode=mode, validate=False)
    print(f'RAW_LEAN_REPORT path={destination} sha256={public.digest(destination)}')


def main():
    actions = {'prepare': prepare, 'module': module, 'aggregate': aggregate, 'publish': publish, 'batch': batch}
    if len(sys.argv) < 2 or sys.argv[1] not in actions:
        raise ValueError('expected prepare, module, aggregate, publish, or batch')
    actions[sys.argv[1]](*sys.argv[2:])


if __name__ == '__main__':
    try:
        main()
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        print(f'lean-inspector-native: {error}', file=sys.stderr)
        raise SystemExit(1)
