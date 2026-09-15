#!/usr/bin/env python3
"""Production actions for Lake's Inspector facets; Lake owns all reuse decisions."""
from __future__ import annotations

import json
from functools import lru_cache
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
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

import materials
import publication as public

selection = public.selection
ROW_SUFFIXES = ('', '.materials.zip', '.provenance.json')
UTILITY_FIELDS = {'modulePath', 'claimGid', 'claimModule', 'claimSelector', 'claimSourcePath',
                  'claimSourceSha256', 'resultGid', 'resultModule', 'resultSelector'}


def activity(kind, count):
    """Invocation-local work counts; these never participate in reuse decisions."""
    path = os.environ.get('STRATALINT_INSPECTOR_ACTIVITY')
    if path:
        with Path(path).open('a', encoding='utf-8') as target:
            target.write(json.dumps({'kind': kind, 'count': count}) + '\n')


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


def prepare(root):
    root = Path(root).resolve()
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
    result = subprocess.run([*command, 'lean-utility-input'],
        cwd=root, stdout=subprocess.PIPE, check=True)
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
    # Membership and public input coordinates affect aggregation only. Each
    # module traces compatibility, config, source, compiler and utility inputs.
    write_if_changed(state(root) / 'inputs.json', materials.canonical_json({
        'modules': sorted(modules),
        'configs': inputs.expand('config_inputs'), 'coordinates': public.coordinates(root)}))


@lru_cache(maxsize=None)
def source_inventory(root):
    # Expanded once per native invocation, never mixed into the aggregate
    # trace: adding an unused producer helper is still a compatible change.
    inputs = selection.Selection(root)
    return set(inputs.dependency_sources()), set(inputs.modules().values())


def input_sources(root, utility_path):
    """Capture Lake's local source closure, bounded by explicit registration.

    Other reported sources are already bound by the complete exported report
    address. Keep their closure out of each row's sidecar to avoid quadratic
    duplication; native compiler traces still govern row invalidation.
    """
    allowed, reported = source_inventory(str(root))
    record = public.read_json(Path(utility_path).read_bytes())
    paths = public.read_json(Path(str(utility_path) + '.sources.json').read_bytes())
    materials.require_sorted_strings(sorted(set(paths)), 'native dependency sources')
    if set(paths) - allowed:
        raise ValueError('unregistered native dependency sources: ' + ', '.join(sorted(set(paths) - allowed)))
    selected = (set(paths) - reported) | {record['source_path']}
    return {path: public.digest(Path(root) / path) for path in sorted(selected)}


def row_binding(rows, root, module_name, utility_path):
    if len(rows) != 1 or rows[0]['module'] != module_name:
        raise ValueError('native module binding mismatch')
    row = rows[0]
    record = public.read_json(Path(utility_path).read_bytes())
    path = record['source_path']
    if row['source_path'] != path or row['source_sha256'] != 'sha256:' + public.digest(Path(root) / path):
        raise ValueError('native module source mismatch')
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
        bindings = input_sources(root, utility_path)
        utility = directory / 'utility.json'
        utility.write_bytes(materials.canonical_json(record['utilities']))
        spool = directory / 'spool'
        spool.mkdir()
        report = directory / public.RAW
        subprocess.run([str(executable), '--output', str(directory / 'spool.json'), '--material-spool', str(spool),
            '--utility-input', str(utility), name, record['source_path'], 'sha256:' + public.digest(source)], check=True, cwd=root)
        materials.compact(directory / 'spool.json', spool, report)
        # Lake returns only canonically validated public facets. Generation is
        # private; the completed artifact gets its full validation at acceptance.
        rows = public.read_json(report.read_bytes())['modules']
        row_binding(rows, root, name, utility_path)
        artifact = directory / 'module.zip'
        public.write_origin(report, name, dict(public.production_origin(root, executable),
                                              input_sources=bindings))
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in ROW_SUFFIXES])
        os.replace(artifact, output)
        activity('extract', 1)
        print(f'LEAN_INSPECTOR_EXTRACT module={name} declarations={len(rows[0]["declarations"])}')


def produce_batch(requests):
    requests = sorted(requests, key=lambda row: row[1])
    root = Path(requests[0][0])
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
            bindings[name] = (utility_path, Path(output), input_sources(root, utility_path))
        utility_file = directory / 'utility.json'
        utility_file.write_bytes(materials.canonical_json(utilities))
        arguments = ['--output', str(directory / 'spool.json'), '--material-spool', str(spool),
                     '--utility-input', str(utility_file), *triples]
        argument_file = directory / 'arguments.json'
        argument_file.write_text(json.dumps(arguments))
        subprocess.run([executable, '--request-file', str(argument_file)], cwd=root, check=True)
        raw = public.read_json((directory / 'spool.json').read_bytes())
        if [row['module'] for row in raw['modules']] != sorted(bindings):
            raise ValueError('incomplete native inspection batch')
        for row in raw['modules']:
            name = row['module']
            utility_path, output, sources = bindings[name]
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
            materials.compact(spool_report, row_spool, report)
            rows = public.read_json(report.read_bytes())['modules']
            row_binding(rows, root, name, utility_path)
            output.parent.mkdir(parents=True, exist_ok=True)
            artifact = row_dir / 'module.zip'
            public.write_origin(report, name, dict(origin, input_sources=sources))
            public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in ROW_SUFFIXES])
            os.replace(artifact, output)
        if list(spool.iterdir()):
            raise ValueError('unreferenced batch materials')
        activity('extract', len(requests))
        print(f'LEAN_INSPECTOR_EXTRACT modules={len(requests)} declarations={sum(len(row["declarations"]) for row in raw["modules"])}')


def batch(request_file, result_file):
    requests = public.read_json(Path(request_file).read_bytes())
    produce = [args for kind, args in requests if kind == 'produce']
    if produce:
        produce_batch(produce)
    statuses = []
    verified_materials = {}
    for kind, args in requests:
        if kind == 'produce':
            statuses.append(0)
        elif kind == 'validate':
            try:
                validate(*args[1:], verified_materials=verified_materials)
                statuses.append(0)
            except (OSError, UnicodeError, ValueError, KeyError, TypeError,
                    zipfile.BadZipFile, zlib.error, NotImplementedError) + LZMA_ERRORS as error:
                print(f'LEAN_INSPECTOR_REJECT {error}', file=sys.stderr)
                statuses.append(1)
        elif kind == 'aggregate':
            if any(statuses):
                statuses.append(1)
            else:
                root, output, *artifacts = args
                aggregate(root, output, artifacts, verified_materials=verified_materials)
                statuses.append(0)
        else:
            raise ValueError('unknown native batch operation')
    Path(result_file).write_text(json.dumps(statuses))


def aggregate(root, output, artifacts, verified_materials=None):
    root, output = Path(root), Path(output)
    config = public.read_json((state(root) / 'inputs.json').read_bytes())
    if len(artifacts) != len(config['modules']):
        raise ValueError('native aggregate membership mismatch')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.aggregate.', dir=output.parent) as directory:
        directory = Path(directory)
        material_dir = directory / 'sha256'
        material_dir.mkdir()
        rows = []
        origins = {}
        for name, artifact in zip(config['modules'], artifacts):
            with tempfile.TemporaryDirectory(prefix='row.', dir=directory) as row_dir:
                report = public.unpack(artifact, row_dir, ROW_SUFFIXES)
                current = public.validate_rows(report, public.member(report, '.materials.zip'), verified_materials)
                row_binding(current, root, name, state(root) / 'inputs' / (name + '.json'))
                origins[name] = public.validate_origin(report, current, config['coordinates']['producer'])
                if origins[name]['input_sources'] != input_sources(root, state(root) / 'inputs' / (name + '.json')):
                    raise ValueError('native dependency source binding mismatch')
                rows.extend(current)
                with zipfile.ZipFile(public.member(report, '.materials.zip')) as archive:
                    for entry in archive.infolist():
                        destination = material_dir / entry.filename[7:]
                        if destination.exists():
                            with destination.open('rb') as left, archive.open(entry) as right:
                                if not materials.streams_equal(left, right):
                                    raise ValueError('statement material address collision')
                        else:
                            with archive.open(entry) as reader, destination.open('wb') as writer:
                                shutil.copyfileobj(reader, writer, materials.BUFFER_BYTES)
        report = directory / public.RAW
        report.write_bytes(materials.canonical_json({'modules': rows, 'schema': materials.REPORT_SCHEMA}))
        with zipfile.ZipFile(public.member(report, '.materials.zip'), 'w', compression=zipfile.ZIP_DEFLATED,
                             compresslevel=6, allowZip64=True) as archive:
            for source in sorted(material_dir.iterdir()):
                info = zipfile.ZipInfo('sha256/' + source.name, materials.ARCHIVE_TIMESTAMP)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                with source.open('rb') as reader, archive.open(info, 'w') as writer:
                    shutil.copyfileobj(reader, writer, materials.BUFFER_BYTES)
        public.write_sidecars(report, config['coordinates'], origins)
        # The native aggregate facet validates the completed bundle before
        # exposing it. Do not repeat that complete pass inside its builder.
        artifact = directory / 'report.zip'
        public.zip_files(artifact, [(public.RAW + suffix, public.member(report, suffix)) for suffix in public.SUFFIXES])
        os.replace(artifact, output)
        activity('aggregate', 1)
        print(f'LEAN_INSPECTOR_AGGREGATE modules={len(rows)} declarations={sum(len(row["declarations"]) for row in rows)}')


def validate(kind, root, *args, verified_materials=None):
    with tempfile.TemporaryDirectory(prefix='.validate.', dir=state(root)) as directory:
        if kind == 'module':
            name, utility, artifact = args
            report = public.unpack(artifact, directory, ROW_SUFFIXES)
            rows = public.validate_rows(report, public.member(report, '.materials.zip'), verified_materials)
            row_binding(rows, root, name, utility)
            # prepare validated the manifest before any facet could accept an
            # artifact. Read its small derived token, not the full module scope
            # again for each row in a large validation batch.
            compatibility = (state(root) / 'compatibility').read_text(encoding='ascii').strip()
            origin = public.validate_origin(report, rows, compatibility)
            if origin['input_sources'] != input_sources(root, utility):
                raise ValueError('native dependency source binding mismatch')
        elif kind == 'report':
            report = public.unpack(args[0], directory)
            config = public.read_json((state(root) / 'inputs.json').read_bytes())
            rows = public.validate_bundle(report, config['coordinates'], root, verified_materials)
            if [row['module'] for row in rows] != config['modules']:
                raise ValueError('native aggregate membership mismatch')
            for row in rows:
                row_binding([row], root, row['module'], state(root) / 'inputs' / (row['module'] + '.json'))
        else:
            raise ValueError('unknown native artifact kind')


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
        public.publish(report, Path(destination), inputs, root, mode=mode)
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
